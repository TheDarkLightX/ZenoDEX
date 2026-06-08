from __future__ import annotations

from typing import Any, Callable


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]

_TWO_POOL_AUDIT_ENDPOINT = "/api/dex/audit_exact_out_two_pool_canonicality"
_MANY_POOL_AUDIT_ENDPOINT = "/api/dex/audit_exact_out_many_pool_canonicality"

_MANY_POOL_AUDIT_DEFAULTS = {
    "max_legs": 3,
    "max_candidate_pools": 5,
    "max_candidates": 12,
    "max_iters": 4096,
    "window": 64,
    "brute_force_max": 512,
    "max_full_domain_pools": 8,
    "max_enumerated_candidates": 20_000,
}

_MANY_POOL_AUDIT_MIN_VALUES = {
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


class _BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _write_bad_request(write_json: WriteJson, exc: _BadRequest) -> None:
    write_json(400, {"ok": False, "error": exc.error})


def _require_assets(obj: dict[str, object]) -> tuple[str, str]:
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        raise _BadRequest("bad_assets")
    return asset_in, asset_out


def _require_int(value: object, *, field_name: str, min_value: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < min_value:
        raise _BadRequest(f"bad_{field_name}")
    return int(value)


def _parse_many_pool_audit_values(obj: dict[str, object]) -> dict[str, int]:
    values = {"amount_out_total": obj.get("amount_out_total")}
    for field_name, default in _MANY_POOL_AUDIT_DEFAULTS.items():
        values[field_name] = obj.get(field_name, default)
    return {
        field_name: _require_int(
            value,
            field_name=field_name,
            min_value=_MANY_POOL_AUDIT_MIN_VALUES[field_name],
        )
        for field_name, value in values.items()
    }


def _handle_two_pool_audit(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        if len(pools_by_id) != 2:
            write_json(400, {"ok": False, "error": "expected_exactly_two_pools"})
            return
        asset_in, asset_out = _require_assets(obj)
        amount_out_total = _require_int(
            obj.get("amount_out_total"),
            field_name="amount_out_total",
            min_value=1,
        )
        brute_force_raw = obj.get("brute_force_max")
        brute_force_max = None
        if brute_force_raw is not None:
            brute_force_max = _require_int(
                brute_force_raw,
                field_name="brute_force_max",
                min_value=0,
            )

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            audit_exact_out_two_pool_runtime_canonicality,
        )

        pools = list(pools_by_id.values())
        audit = audit_exact_out_two_pool_runtime_canonicality(
            pools[0],
            pools[1],
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out_total,
            brute_force_max=brute_force_max,
        )
        write_json(200, {"ok": True, "audit": audit.to_dict()})
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {
                "ok": False,
                "error": "audit_exact_out_two_pool_canonicality_error",
                "details": "request failed",
            },
        )


def _handle_many_pool_audit(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        asset_in, asset_out = _require_assets(obj)
        values = _parse_many_pool_audit_values(obj)

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            audit_exact_out_many_pool_runtime_canonicality,
        )

        audit = audit_exact_out_many_pool_runtime_canonicality(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **values,
        )
        write_json(200, {"ok": True, "audit": audit.to_dict()})
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {
                "ok": False,
                "error": "audit_exact_out_many_pool_canonicality_error",
                "details": "request failed",
            },
        )


def maybe_handle_exact_out_audit_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    if path == _TWO_POOL_AUDIT_ENDPOINT:
        _handle_two_pool_audit(obj, parse_pools, write_json)
        return True
    if path == _MANY_POOL_AUDIT_ENDPOINT:
        _handle_many_pool_audit(obj, parse_pools, write_json)
        return True
    return False
