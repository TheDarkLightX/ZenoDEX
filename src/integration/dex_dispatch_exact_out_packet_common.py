"""Shared exact-out packet-builder helpers for DEX dispatch modules."""

from __future__ import annotations

import importlib
from dataclasses import dataclass
from typing import Any, Mapping, Optional, Sequence

from src.integration._dex_api_helpers import IntFieldSpec, parse_int_kwargs, parse_pools
from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse

_PACKET_BUILDER_DEFAULT_FIELDS: list[tuple[str, Any, int]] = [
    ("amount_out_total", None, 1),
    ("max_legs", 3, 1),
    ("max_candidate_pools", 5, 1),
    ("max_candidates", 12, 1),
    ("max_iters", 4096, 1),
    ("window", 64, 0),
    ("brute_force_max", 512, 0),
    ("max_full_domain_pools", 8, 1),
    ("max_enumerated_candidates", 20_000, 1),
]


def _int_field_specs_from_tuples(
    tuples: Sequence[tuple[str, Any, int]],
) -> tuple[IntFieldSpec, ...]:
    """Convert the legacy ``(name, default, minimum)`` tuple form into specs."""
    return tuple(IntFieldSpec(name=n, default=d, minimum=m) for n, d, m in tuples)


@dataclass(frozen=True)
class _ExactOutPacketResponseSpec:
    schema: str
    verify_endpoint: str
    quote_policy: Optional[str]
    response_mode: str
    fallback_error: Optional[str]
    extra_response_field: Optional[tuple[str, str]]


@dataclass(frozen=True)
class _ExactOutPacketBuilderSpec:
    field_specs: Sequence[IntFieldSpec]
    module_function_name: str
    module_schema_name: str
    verify_endpoint: str
    error_code: str
    quote_policy: Optional[str] = None
    response_mode: str = "ok_packet_ok"
    fallback_error: Optional[str] = None
    extra_response_field: Optional[tuple[str, str]] = None


def _exact_out_packet_response_base(
    *,
    ok: bool,
    packet: Any,
    spec: _ExactOutPacketResponseSpec,
) -> dict[str, Any]:
    response: dict[str, Any] = {
        "ok": ok,
        "packet": packet.to_dict(),
        "packet_schema": spec.schema,
        "verify_packet_endpoint": spec.verify_endpoint,
    }
    if spec.quote_policy is not None:
        response["quote_policy"] = spec.quote_policy
    return response


def _exact_out_packet_response(
    *,
    packet: Any,
    spec: _ExactOutPacketResponseSpec,
) -> dict[str, Any]:
    if spec.response_mode == "ok_true":
        response = _exact_out_packet_response_base(
            ok=True,
            packet=packet,
            spec=spec,
        )
    elif spec.response_mode == "ok_packet_ok":
        response = _exact_out_packet_response_base(
            ok=bool(packet.packet_ok),
            packet=packet,
            spec=spec,
        )
        if not packet.packet_ok and spec.fallback_error is not None:
            response["error"] = str(getattr(packet, "error", None) or spec.fallback_error)
    else:
        response = _exact_out_packet_response_base(
            ok=True,
            packet=packet,
            spec=spec,
        )
        if not packet.packet_ok:
            response["ok"] = False
            response["error"] = str(packet.error or spec.fallback_error or "packet_not_ok")

    if spec.extra_response_field is not None:
        response_key, packet_attr = spec.extra_response_field
        response[response_key] = bool(getattr(packet, packet_attr))
    return response


def _make_exact_out_many_pool_packet_builder(spec: _ExactOutPacketBuilderSpec) -> Any:
    """Factory for build_exact_out_many_pool_*_packet endpoints."""
    if spec.response_mode not in {"ok_true", "ok_packet_ok", "ok_true_unless_packet_ok"}:
        raise ValueError(f"unknown response_mode: {spec.response_mode}")

    def _handler(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
        pools_by_id = parse_pools(obj)
        asset_in = str(obj.get("asset_in", "")).strip()
        asset_out = str(obj.get("asset_out", "")).strip()
        if not asset_in or not asset_out or asset_in == asset_out:
            return 400, {"ok": False, "error": "bad_assets"}

        int_kwargs = parse_int_kwargs(obj, spec.field_specs)

        module = importlib.import_module("src.integration.exact_out_route_certificate")
        builder = getattr(module, spec.module_function_name)
        schema = getattr(module, spec.module_schema_name)

        packet = builder(
            list(pools_by_id.values()),
            asset_in=asset_in,
            asset_out=asset_out,
            **int_kwargs,
        )
        return 200, _exact_out_packet_response(
            packet=packet,
            spec=_ExactOutPacketResponseSpec(
                schema=schema,
                verify_endpoint=spec.verify_endpoint,
                quote_policy=spec.quote_policy,
                response_mode=spec.response_mode,
                fallback_error=spec.fallback_error,
                extra_response_field=spec.extra_response_field,
            ),
        )

    return _handler
