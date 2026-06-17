"""Exact-out advisory quote handlers for the DEX dispatch registry."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.integration._dex_api_helpers import (
    parse_pools,
    projected_path_from_exact_out_quote_payload,
)
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register
from src.integration.dex_dispatch_exact_out_packet_common import _PACKET_BUILDER_DEFAULT_FIELDS

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (ImportError, TypeError, ValueError, ArithmeticError)


@dataclass(frozen=True)
class _ExactOutQuoteInputs:
    pools: list[Any]
    asset_in: str
    asset_out: str
    int_kwargs: dict[str, int]


@dataclass(frozen=True)
class _BoundedProjectionContext:
    quote_source: str
    selected_cover: Mapping[str, Any] | None
    repaired_cover: Mapping[str, Any] | None
    runtime_projected_path: object
    advisory_projected_path: object


def _bad_request(error: str) -> DexResponse:
    return 400, {"ok": False, "error": error}


def _parse_quote_inputs(obj: Mapping[str, Any]) -> DexResponse | _ExactOutQuoteInputs:
    pools_by_id = parse_pools(obj)
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        return _bad_request("bad_assets")

    int_kwargs: dict[str, int] = {}
    for field_name, default, min_value in _PACKET_BUILDER_DEFAULT_FIELDS:
        value = obj.get(field_name, default)
        if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
            return _bad_request(f"bad_{field_name}")
        int_kwargs[field_name] = int(value)

    return _ExactOutQuoteInputs(
        pools=list(pools_by_id.values()),
        asset_in=asset_in,
        asset_out=asset_out,
        int_kwargs=int_kwargs,
    )


def _projected_path(payload: object) -> list[list[object]] | None:
    return projected_path_from_exact_out_quote_payload(payload)


def _cover_canonical_path(cover: Mapping[str, Any] | None) -> Any:
    return None if cover is None else cover["canonical_quote_projected_path"]


def _cover_holds(cover: Mapping[str, Any] | None) -> bool | None:
    return None if cover is None else bool(cover["projection_cover_holds"])


def _projection_path_match(left: object, right: object) -> bool | None:
    if left is None or right is None:
        return None
    return bool(left == right)


def _handle_quote_exact_out_many_pool_repaired_selected_domain(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    try:
        inputs = _parse_quote_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            quote_exact_out_many_pool_repaired_selected_domain,
        )

        quote, err, contract = quote_exact_out_many_pool_repaired_selected_domain(
            inputs.pools,
            asset_in=inputs.asset_in,
            asset_out=inputs.asset_out,
            **inputs.int_kwargs,
        )
        contract_payload = contract.to_dict()
        return 200, _repaired_selected_domain_payload(
            quote=quote,
            err=err,
            contract_payload=contract_payload,
        )
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "quote_exact_out_many_pool_repaired_selected_domain_error",
            "details": "request failed",
        }


def _repaired_selected_domain_payload(*, quote: Any, err: Any, contract_payload: Mapping[str, Any]) -> dict[str, Any]:
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
        "audit_pool_ids_match_repaired_selected_pool_ids": contract_payload["audit_pool_ids_match_repaired_selected_pool_ids"],
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


def _handle_quote_exact_out_many_pool_repaired_advisory(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    try:
        inputs = _parse_quote_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA,
            quote_exact_out_many_pool_repaired_advisory,
        )

        quote, err, packet = quote_exact_out_many_pool_repaired_advisory(
            inputs.pools,
            asset_in=inputs.asset_in,
            asset_out=inputs.asset_out,
            **inputs.int_kwargs,
        )
        return 200, _repaired_advisory_payload(
            quote=quote,
            err=err,
            packet=packet,
            schema=EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA,
        )
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "quote_exact_out_many_pool_repaired_advisory_error",
            "details": "request failed",
        }


def _repaired_advisory_payload(*, quote: Any, err: Any, packet: Any, schema: str) -> dict[str, Any]:
    packet_payload = packet.to_dict()
    runtime_quote_payload = packet_payload["runtime_quote"]
    advisory_quote_payload = packet_payload["advisory_quote"]
    repaired_projection_cover = packet_payload["projection_cover_audit"]
    advisory_projected_path = _projected_path(advisory_quote_payload)
    repaired_canonical_projected_path = _cover_canonical_path(repaired_projection_cover)
    payload = {
        "ok": bool(quote is not None),
        "packet": packet_payload,
        "packet_schema": schema,
        "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet",
        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
        "runtime_quote": runtime_quote_payload,
        "runtime_matches_advisory": bool(packet.runtime_matches_advisory),
        "runtime_projected_path": _projected_path(runtime_quote_payload),
        "advisory_projected_path": advisory_projected_path,
        "repaired_projection_cover_available": bool(repaired_projection_cover is not None),
        "repaired_projection_cover_holds": _cover_holds(repaired_projection_cover),
        "repaired_canonical_projected_path": repaired_canonical_projected_path,
        "effective_projection_cover_side": "repaired" if quote is not None else None,
        "effective_projection_cover_holds": _cover_holds(repaired_projection_cover),
        "effective_canonical_projected_path": repaired_canonical_projected_path,
        "effective_quote_projected_path": advisory_projected_path,
        "effective_quote_matches_canonical_projected_path": _projection_path_match(
            advisory_projected_path,
            repaired_canonical_projected_path,
        ),
    }
    if quote is not None:
        payload["quote"] = advisory_quote_payload
    else:
        payload["error"] = str(err or "many_pool_repaired_prefilter_contract_not_ok")
    return payload


def _bounded_effective_fields(ctx: _BoundedProjectionContext) -> dict[str, Any]:
    if ctx.quote_source == "selected_domain_runtime":
        side = "selected_domain"
        cover = ctx.selected_cover
        quote_path = ctx.runtime_projected_path
    elif ctx.quote_source == "repaired_bounded_advisory":
        side = "repaired"
        cover = ctx.repaired_cover
        quote_path = ctx.advisory_projected_path
    else:
        side = None
        cover = None
        quote_path = None
    canonical_path = _cover_canonical_path(cover)
    return {
        "effective_projection_cover_side": side,
        "effective_projection_cover_holds": _cover_holds(cover),
        "effective_canonical_projected_path": canonical_path,
        "effective_quote_projected_path": quote_path,
        "effective_quote_matches_canonical_projected_path": _projection_path_match(quote_path, canonical_path),
    }


def _bounded_advisory_payload(*, quote: Any, err: Any, packet: Any, schema: str) -> dict[str, Any]:
    packet_payload = packet.to_dict()
    selected_cover = packet_payload["workaround_packet"]["oracle_contract"]["audit"]["projection_cover_audit"]
    repaired_cover = packet_payload["workaround_packet"]["repaired_packet"]["projection_cover_audit"]
    runtime_quote_payload = packet_payload["workaround_packet"]["oracle_contract"]["audit"]["runtime_quote"]
    advisory_quote_payload = packet_payload["advisory_quote"]
    runtime_projected_path = _projected_path(runtime_quote_payload)
    advisory_projected_path = _projected_path(advisory_quote_payload)
    payload = {
        "ok": bool(quote is not None),
        "packet": packet_payload,
        "packet_schema": schema,
        "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet",
        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
        "runtime_quote": runtime_quote_payload,
        "quote_source": packet.quote_source,
        "repaired_advisory_available": bool(packet.repaired_advisory_available),
        "quote_matches_runtime": bool(packet.quote_matches_runtime),
        "quote_matches_repaired_advisory": bool(packet.quote_matches_repaired_advisory),
        "runtime_projected_path": runtime_projected_path,
        "advisory_projected_path": advisory_projected_path,
        "selected_domain_projection_cover_available": bool(selected_cover is not None),
        "selected_domain_projection_cover_holds": _cover_holds(selected_cover),
        "selected_domain_canonical_projected_path": _cover_canonical_path(selected_cover),
        "selected_runtime_matches_selected_canonical_projected_path": _projection_path_match(
            runtime_projected_path,
            _cover_canonical_path(selected_cover),
        ),
        "repaired_projection_cover_available": bool(repaired_cover is not None),
        "repaired_projection_cover_holds": _cover_holds(repaired_cover),
        "repaired_canonical_projected_path": _cover_canonical_path(repaired_cover),
        "advisory_matches_repaired_canonical_projected_path": _projection_path_match(
            advisory_projected_path,
            _cover_canonical_path(repaired_cover),
        ),
        **_bounded_effective_fields(_BoundedProjectionContext(
            quote_source=packet.quote_source,
            selected_cover=selected_cover,
            repaired_cover=repaired_cover,
            runtime_projected_path=runtime_projected_path,
            advisory_projected_path=advisory_projected_path,
        )),
    }
    if quote is not None:
        payload["quote"] = advisory_quote_payload
    else:
        payload["error"] = str(err or "many_pool_bounded_advisory_unavailable")
    return payload


def _handle_quote_exact_out_many_pool_bounded_advisory(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    try:
        inputs = _parse_quote_inputs(obj)
        if isinstance(inputs, tuple):
            return inputs

        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
            quote_exact_out_many_pool_bounded_advisory,
        )

        quote, err, packet = quote_exact_out_many_pool_bounded_advisory(
            inputs.pools,
            asset_in=inputs.asset_in,
            asset_out=inputs.asset_out,
            **inputs.int_kwargs,
        )
        return 200, _bounded_advisory_payload(
            quote=quote,
            err=err,
            packet=packet,
            schema=EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
        )
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "quote_exact_out_many_pool_bounded_advisory_error",
            "details": "request failed",
        }


_register(
    "/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
    _handle_quote_exact_out_many_pool_repaired_selected_domain,
)
_register(
    "/api/dex/quote_exact_out_many_pool_repaired_advisory",
    _handle_quote_exact_out_many_pool_repaired_advisory,
)
_register(
    "/api/dex/quote_exact_out_many_pool_bounded_advisory",
    _handle_quote_exact_out_many_pool_bounded_advisory,
)
