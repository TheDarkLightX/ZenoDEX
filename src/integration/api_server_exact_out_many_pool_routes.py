from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]
ProjectQuotePath = Callable[[object], list[list[object]] | None]
RouteHandler = Callable[[dict[str, object], ParsePools, ProjectQuotePath, WriteJson], None]
SimpleRouteHandler = Callable[[dict[str, object], ParsePools, WriteJson], None]

# The parent HTTP handler applies exact-out upper caps before dispatching here.
# These handlers preserve the old per-route parse order and lower-bound errors.
_CANDIDATE_DOMAIN_ENDPOINT = "/api/dex/build_exact_out_many_pool_candidate_domain_contract"
_PREFILTER_ENDPOINT = "/api/dex/build_exact_out_many_pool_prefilter_contract"
_REPAIRED_PREFILTER_ENDPOINT = "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract"
_REPAIRED_SELECTED_DOMAIN_ENDPOINT = (
    "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract"
)
_REPAIRED_SELECTED_DOMAIN_QUOTE_ENDPOINT = "/api/dex/quote_exact_out_many_pool_repaired_selected_domain"
_REPAIRED_ADVISORY_QUOTE_ENDPOINT = "/api/dex/quote_exact_out_many_pool_repaired_advisory"
_REPAIRED_FULL_DOMAIN_CERTIFIED_QUOTE_ENDPOINT = (
    "/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified"
)
_BOUNDED_ADVISORY_QUOTE_ENDPOINT = "/api/dex/quote_exact_out_many_pool_bounded_advisory"

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

_MAX_VALUES = {
    "amount_out_total": 50_000,
    "max_legs": 3,
    "max_candidate_pools": 5,
    "max_candidates": 12,
    "max_iters": 4_096,
    "window": 64,
    "brute_force_max": 512,
    "max_full_domain_pools": 16,
    "max_enumerated_candidates": 50_000,
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


def _int_in_range(value: int, name: str) -> bool:
    return _MIN_VALUES[name] <= value <= _MAX_VALUES[name]


def _require_int(obj: dict[str, object], name: str) -> int:
    value = obj.get(name, _DEFAULTS.get(name))
    if not isinstance(value, int) or isinstance(value, bool) or not _int_in_range(value, name):
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


def _repaired_advisory_quote_payload(
    *,
    quote: object,
    err: object,
    packet_payload: dict[str, object],
    runtime_projected_path: list[list[object]] | None,
    advisory_projected_path: list[list[object]] | None,
) -> dict[str, object]:
    projection_cover = packet_payload["projection_cover_audit"]
    payload = {
        "ok": bool(quote is not None),
        "packet": packet_payload,
        "packet_schema": packet_payload["schema"],
        "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet",
        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
        "runtime_quote": packet_payload["runtime_quote"],
        "runtime_matches_advisory": bool(packet_payload["runtime_matches_advisory"]),
        "runtime_projected_path": runtime_projected_path,
        "advisory_projected_path": advisory_projected_path,
    }
    payload.update(
        _repaired_advisory_projection_payload(
            projection_cover=projection_cover,
            advisory_projected_path=advisory_projected_path,
            quote_available=quote is not None,
        )
    )
    if quote is not None:
        payload["quote"] = packet_payload["advisory_quote"]
    else:
        payload["error"] = str(err or "many_pool_repaired_prefilter_contract_not_ok")
    return payload


def _repaired_advisory_projection_payload(
    *,
    projection_cover: object,
    advisory_projected_path: list[list[object]] | None,
    quote_available: bool,
) -> dict[str, object]:
    canonical_projected_path = (
        None if projection_cover is None else projection_cover["canonical_quote_projected_path"]
    )
    projection_cover_holds = (
        None if projection_cover is None else bool(projection_cover["projection_cover_holds"])
    )
    return {
        "repaired_projection_cover_available": bool(projection_cover is not None),
        "repaired_projection_cover_holds": projection_cover_holds,
        "repaired_canonical_projected_path": canonical_projected_path,
        "effective_projection_cover_side": "repaired" if quote_available else None,
        "effective_projection_cover_holds": projection_cover_holds,
        "effective_canonical_projected_path": canonical_projected_path,
        "effective_quote_projected_path": advisory_projected_path,
        "effective_quote_matches_canonical_projected_path": _projected_path_matches(
            advisory_projected_path,
            canonical_projected_path,
        ),
    }


def _projected_path_matches(
    actual: list[list[object]] | None,
    expected: object,
) -> bool | None:
    if actual is None or expected is None:
        return None
    return bool(actual == expected)


def _projection_cover_path(projection_cover: object) -> object:
    return None if projection_cover is None else projection_cover["canonical_quote_projected_path"]


def _projection_cover_holds(projection_cover: object) -> bool | None:
    return None if projection_cover is None else bool(projection_cover["projection_cover_holds"])


def _handle_repaired_advisory_quote(
    obj: dict[str, object],
    parse_pools: ParsePools,
    project_quote_path: ProjectQuotePath,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(obj, parse_pools, tuple(_MIN_VALUES))
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            quote_exact_out_many_pool_repaired_advisory,
        )

        quote, err, packet = quote_exact_out_many_pool_repaired_advisory(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            **req.values,
        )
        packet_payload = packet.to_dict()
        payload = _repaired_advisory_quote_payload(
            quote=quote,
            err=err,
            packet_payload=packet_payload,
            runtime_projected_path=project_quote_path(packet_payload["runtime_quote"]),
            advisory_projected_path=project_quote_path(packet_payload["advisory_quote"]),
        )
        write_json(200, payload)
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "quote_exact_out_many_pool_repaired_advisory_error", "details": "request failed"},
        )


def _bounded_effective_projection_payload(
    *,
    quote_source: object,
    runtime_projected_path: list[list[object]] | None,
    advisory_projected_path: list[list[object]] | None,
    selected_canonical_projected_path: object,
    repaired_canonical_projected_path: object,
    selected_projection_cover: object,
    repaired_projection_cover: object,
) -> dict[str, object]:
    if quote_source == "selected_domain_runtime":
        return {
            "effective_projection_cover_side": "selected_domain",
            "effective_projection_cover_holds": _projection_cover_holds(selected_projection_cover),
            "effective_canonical_projected_path": selected_canonical_projected_path,
            "effective_quote_projected_path": runtime_projected_path,
        }
    if quote_source == "repaired_bounded_advisory":
        return {
            "effective_projection_cover_side": "repaired",
            "effective_projection_cover_holds": _projection_cover_holds(repaired_projection_cover),
            "effective_canonical_projected_path": repaired_canonical_projected_path,
            "effective_quote_projected_path": advisory_projected_path,
        }
    return {
        "effective_projection_cover_side": None,
        "effective_projection_cover_holds": None,
        "effective_canonical_projected_path": None,
        "effective_quote_projected_path": None,
    }


def _bounded_projection_payload(
    packet_payload: dict[str, object],
    project_quote_path: ProjectQuotePath,
) -> dict[str, object]:
    workaround_packet = packet_payload["workaround_packet"]
    oracle_audit = workaround_packet["oracle_contract"]["audit"]
    selected_cover = oracle_audit["projection_cover_audit"]
    repaired_cover = workaround_packet["repaired_packet"]["projection_cover_audit"]
    runtime_projected_path = project_quote_path(oracle_audit["runtime_quote"])
    advisory_projected_path = project_quote_path(packet_payload["advisory_quote"])
    selected_path = _projection_cover_path(selected_cover)
    repaired_path = _projection_cover_path(repaired_cover)
    payload = {
        "runtime_projected_path": runtime_projected_path,
        "advisory_projected_path": advisory_projected_path,
        "selected_domain_projection_cover_available": bool(selected_cover is not None),
        "selected_domain_projection_cover_holds": _projection_cover_holds(selected_cover),
        "selected_domain_canonical_projected_path": selected_path,
        "selected_runtime_matches_selected_canonical_projected_path": _projected_path_matches(
            runtime_projected_path,
            selected_path,
        ),
        "repaired_projection_cover_available": bool(repaired_cover is not None),
        "repaired_projection_cover_holds": _projection_cover_holds(repaired_cover),
        "repaired_canonical_projected_path": repaired_path,
        "advisory_matches_repaired_canonical_projected_path": _projected_path_matches(
            advisory_projected_path,
            repaired_path,
        ),
    }
    payload.update(
        _bounded_effective_projection_payload(
            quote_source=packet_payload["quote_source"],
            runtime_projected_path=runtime_projected_path,
            advisory_projected_path=advisory_projected_path,
            selected_canonical_projected_path=selected_path,
            repaired_canonical_projected_path=repaired_path,
            selected_projection_cover=selected_cover,
            repaired_projection_cover=repaired_cover,
        )
    )
    payload["effective_quote_matches_canonical_projected_path"] = _projected_path_matches(
        payload["effective_quote_projected_path"],
        payload["effective_canonical_projected_path"],
    )
    return payload


def _bounded_advisory_quote_payload(
    *,
    quote: object,
    err: object,
    packet_payload: dict[str, object],
    packet_schema: str,
    project_quote_path: ProjectQuotePath,
) -> dict[str, object]:
    oracle_audit = packet_payload["workaround_packet"]["oracle_contract"]["audit"]
    payload = {
        "ok": bool(quote is not None),
        "packet": packet_payload,
        "packet_schema": packet_schema,
        "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet",
        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
        "runtime_quote": oracle_audit["runtime_quote"],
        "quote_source": packet_payload["quote_source"],
        "repaired_advisory_available": bool(packet_payload["repaired_advisory_available"]),
        "quote_matches_runtime": bool(packet_payload["quote_matches_runtime"]),
        "quote_matches_repaired_advisory": bool(packet_payload["quote_matches_repaired_advisory"]),
    }
    payload.update(_bounded_projection_payload(packet_payload, project_quote_path))
    if quote is not None:
        payload["quote"] = packet_payload["advisory_quote"]
    else:
        payload["error"] = str(err or "many_pool_bounded_advisory_unavailable")
    return payload


def _handle_bounded_advisory_quote(
    obj: dict[str, object],
    parse_pools: ParsePools,
    project_quote_path: ProjectQuotePath,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(obj, parse_pools, tuple(_MIN_VALUES))
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
            quote_exact_out_many_pool_bounded_advisory,
        )

        quote, err, packet = quote_exact_out_many_pool_bounded_advisory(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            **req.values,
        )
        write_json(
            200,
            _bounded_advisory_quote_payload(
                quote=quote,
                err=err,
                packet_payload=packet.to_dict(),
                packet_schema=EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
                project_quote_path=project_quote_path,
            ),
        )
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "quote_exact_out_many_pool_bounded_advisory_error", "details": "request failed"},
        )


def _repaired_full_domain_certified_payload(
    *,
    quote: object,
    err: object,
    packet_payload: dict[str, object],
    packet_schema: str,
) -> dict[str, object]:
    repaired_packet = packet_payload["repaired_packet"]
    payload = {
        "ok": bool(quote is not None),
        "packet": packet_payload,
        "packet_schema": packet_schema,
        "quote_policy": "repaired_full_domain_certified_v1",
        "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet",
        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
        "runtime_quote": repaired_packet["runtime_quote"],
        "full_domain_canonical_quote": packet_payload["full_domain_canonical_quote"],
        "repaired_matches_full_canonical": bool(packet_payload["repaired_matches_full_canonical"]),
        "full_domain_candidate_count": int(packet_payload["full_domain_candidate_count"]),
        "full_domain_feasible_pool_ids": [str(pool_id) for pool_id in packet_payload["full_domain_feasible_pool_ids"]],
    }
    if quote is not None:
        payload["quote"] = packet_payload["repaired_quote"]
    else:
        payload["error"] = str(err or "many_pool_repaired_advisory_not_full_domain_canonical")
    return payload


def _handle_repaired_full_domain_certified_quote(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(obj, parse_pools, tuple(_MIN_VALUES))
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
            quote_exact_out_many_pool_repaired_full_domain_certified,
        )

        quote, err, packet = quote_exact_out_many_pool_repaired_full_domain_certified(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            **req.values,
        )
        write_json(
            200,
            _repaired_full_domain_certified_payload(
                quote=quote,
                err=err,
                packet_payload=packet.to_dict(),
                packet_schema=EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
            ),
        )
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {
                "ok": False,
                "error": "quote_exact_out_many_pool_repaired_full_domain_certified_error",
                "details": "request failed",
            },
        )


def maybe_handle_exact_out_many_pool_route(
    *, path: str, obj: dict[str, object], parse_pools: ParsePools,
    project_quote_path: ProjectQuotePath, write_json: WriteJson
) -> bool:
    handler = _ROUTE_HANDLERS.get(path)
    if handler is None:
        return False
    handler(obj, parse_pools, project_quote_path, write_json)
    return True


def _simple_route(handler: SimpleRouteHandler) -> RouteHandler:
    return lambda obj, parse_pools, _project_quote_path, write_json: handler(obj, parse_pools, write_json)


_ROUTE_HANDLERS: dict[str, RouteHandler] = {
    _CANDIDATE_DOMAIN_ENDPOINT: _simple_route(_handle_candidate_domain_contract),
    _PREFILTER_ENDPOINT: _simple_route(_handle_prefilter_contract),
    _REPAIRED_PREFILTER_ENDPOINT: _simple_route(_handle_repaired_prefilter_contract),
    _REPAIRED_SELECTED_DOMAIN_ENDPOINT: _simple_route(_handle_repaired_selected_domain_contract),
    _REPAIRED_SELECTED_DOMAIN_QUOTE_ENDPOINT: _simple_route(_handle_repaired_selected_domain_quote),
    _REPAIRED_ADVISORY_QUOTE_ENDPOINT: _handle_repaired_advisory_quote,
    _REPAIRED_FULL_DOMAIN_CERTIFIED_QUOTE_ENDPOINT: _simple_route(_handle_repaired_full_domain_certified_quote),
    _BOUNDED_ADVISORY_QUOTE_ENDPOINT: _handle_bounded_advisory_quote,
}
