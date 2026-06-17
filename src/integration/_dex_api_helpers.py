"""Shared HTTP helpers for the DEX API dispatch surface.

These helpers replace duplicated ad-hoc validation patterns inside
``src/integration/api_server.py::_Handler._maybe_handle_dex_api``. Each
helper returns a `DexResponse = (status, body)` tuple on error so the
caller can ``self._write_json(*err, cors_origin=cors_origin)`` without
introducing any new mutable state.

Boundary semantics are pinned by ``tests/integration/test_dex_api_helpers.py``:
``bool`` values are rejected even though ``isinstance(True, int)`` is True,
inclusive bounds, JSON objects only (no arrays / nulls / scalars).
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Mapping, Optional, Sequence, Tuple

DexResponse = Tuple[int, Mapping[str, Any]]


class BadFieldError(ValueError):
    """Raised by ``int_field`` / ``optional_int_list_field`` on validation failure.

    Subclasses ``ValueError`` so existing ``except Exception`` and
    ``except (ValueError, TypeError)`` chains still catch it. Callers may
    map it to a 400 response by reading ``err.field`` and ``err.reason``.
    """

    def __init__(self, field: str, reason: str) -> None:
        self.field = field
        self.reason = reason
        super().__init__(f"{field}: {reason}")


def _is_bool(value: Any) -> bool:
    return isinstance(value, bool)


def int_field(
    obj: Mapping[str, Any],
    name: str,
    *,
    default: Optional[int] = None,
    minimum: Optional[int] = None,
    maximum: Optional[int] = None,
) -> int:
    """Read a bounded integer field from a JSON object.

    Rejects ``bool`` values, non-int types, and out-of-range values via
    ``BadFieldError`` (subclass of ``ValueError``). Returns ``default``
    when the key is absent and ``default`` is provided.
    """
    if name not in obj:
        if default is None:
            raise BadFieldError(name, "field is required")
        value: Any = default
    else:
        value = obj[name]
    if _is_bool(value) or not isinstance(value, int):
        raise BadFieldError(name, "must be an int (bool rejected)")
    if minimum is not None and value < minimum:
        raise BadFieldError(name, f"must be >= {minimum}")
    if maximum is not None and value > maximum:
        raise BadFieldError(name, f"must be <= {maximum}")
    return value


def optional_int_list_field(
    obj: Mapping[str, Any],
    name: str,
    *,
    item_minimum: Optional[int] = None,
    item_maximum: Optional[int] = None,
    max_length: Optional[int] = None,
) -> Optional[list[int]]:
    """Read an optional list of bounded ints. Returns None if absent or null."""
    if name not in obj:
        return None
    raw = obj[name]
    if raw is None:
        return None
    if not isinstance(raw, list):
        raise BadFieldError(name, "must be a list of ints")
    if max_length is not None and len(raw) > max_length:
        raise BadFieldError(name, f"must have at most {max_length} items")
    out: list[int] = []
    for idx, item in enumerate(raw):
        if _is_bool(item) or not isinstance(item, int):
            raise BadFieldError(name, f"item {idx} must be an int (bool rejected)")
        if item_minimum is not None and item < item_minimum:
            raise BadFieldError(name, f"item {idx} must be >= {item_minimum}")
        if item_maximum is not None and item > item_maximum:
            raise BadFieldError(name, f"item {idx} must be <= {item_maximum}")
        out.append(item)
    return out


def error_response(status: int, error: str, **details: Any) -> DexResponse:
    """Build a (status, body) tuple matching the legacy error shape.

    Body always carries ``{"ok": False, "error": <code>}`` plus any
    additional ``details`` kwargs. Matches the existing pattern at
    ``api_server.py`` ~lines 1430–1437 and 3925.
    """
    body: dict[str, Any] = {"ok": False, "error": error}
    body.update(details)
    return status, body


def parse_json_body_or_400(raw_body: Optional[bytes]) -> Tuple[Optional[dict[str, Any]], Optional[DexResponse]]:
    """Parse a request body and return (obj, None) or (None, error_response).

    Only JSON objects are accepted: arrays, scalars, and nulls return
    ``bad_body``. Malformed JSON, empty bodies, and decode errors return
    ``bad_json``. Missing body returns ``missing_body``.

    Matches the legacy guards at ``api_server.py:1426-1437``.
    """
    if raw_body is None:
        return None, error_response(400, "missing_body")
    try:
        obj = json.loads(raw_body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, error_response(400, "bad_json")
    if not isinstance(obj, dict):
        return None, error_response(400, "bad_body")
    return obj, None


# ----------------------------------------------------------------------
# Shared parsing helpers extracted from ``_maybe_handle_dex_api`` closures.
# 38+ legacy endpoints called ``_parse_pools``; ``_quote_to_dict`` and the
# split-quote helpers are used by the exact_in / exact_out route handlers.
# ----------------------------------------------------------------------
def parse_pools(obj: Mapping[str, Any]) -> dict[str, Any]:
    """Parse the ``pools`` array from a request body into a {pool_id: PoolState}.

    Mirrors the legacy closure at ``api_server.py:1461-1494``. Raises
    ``ValueError`` on malformed input; callers should catch and return a 400.
    """
    from src.state.pools import PoolState, PoolStatus  # pylint: disable=import-outside-toplevel

    pools_raw = obj.get("pools")
    if not isinstance(pools_raw, list) or not pools_raw:
        raise ValueError("pools must be a non-empty list")
    pools_by_id: dict[str, PoolState] = {}
    for row in pools_raw:
        if not isinstance(row, dict):
            raise ValueError("pool must be an object")
        pid = row.get("pool_id")
        if not isinstance(pid, str) or not pid:
            raise ValueError("pool_id must be a non-empty string")
        if pid in pools_by_id:
            raise ValueError(f"duplicate pool_id: {pid}")
        st_raw = str(row.get("status", "ACTIVE")).strip().upper()
        try:
            st = PoolStatus[st_raw]
        except KeyError as exc:
            raise ValueError(f"bad pool status: {st_raw}") from exc
        pools_by_id[pid] = PoolState(
            pool_id=pid,
            asset0=str(row.get("asset0", "")),
            asset1=str(row.get("asset1", "")),
            reserve0=int_field(row, "reserve0", default=0),
            reserve1=int_field(row, "reserve1", default=0),
            fee_bps=int_field(row, "fee_bps", default=0),
            lp_supply=int_field(row, "lp_supply", default=1),
            status=st,
            created_at=int_field(row, "created_at", default=0),
            curve_tag=str(row.get("curve_tag", "CPMM")),
            curve_params=row.get("curve_params", ""),
        )
    return pools_by_id


def quote_to_dict(q: object) -> dict[str, object]:
    """Convert a RouteQuote into the legacy JSON shape.

    Mirrors the closure at ``api_server.py:1496-1528``.
    """
    from src.core.routing import RouteQuote  # pylint: disable=import-outside-toplevel

    if not isinstance(q, RouteQuote):
        return {}
    legs_out = []
    for leg in q.legs:
        hops_out = []
        for hop in leg.hops:
            hops_out.append(
                {
                    "pool_id": hop.pool_id,
                    "asset_in": hop.asset_in,
                    "asset_out": hop.asset_out,
                    "amount_in": int(hop.amount_in),
                    "amount_out": int(hop.amount_out),
                }
            )
        legs_out.append(
            {
                "amount_in": int(leg.amount_in),
                "amount_out": int(leg.amount_out),
                "hops": hops_out,
            }
        )
    return {
        "asset_in": q.asset_in,
        "asset_out": q.asset_out,
        "amount_in": int(q.amount_in),
        "amount_out": int(q.amount_out),
        "legs": legs_out,
    }


def exact_out_split_quote_from_dict(payload: object) -> Any:
    """Parse an exact-out split quote payload into a SplitManyPoolsExactOutQuote.

    Mirrors the closure at ``api_server.py:1530-1573``. Raises ``ValueError``
    with a specific error code (e.g. ``bad_exact_out_quote``) on malformed
    input.
    """
    from src.core.split_routing_dispatch import (  # pylint: disable=import-outside-toplevel
        SplitLegExactOutQuote,
        SplitManyPoolsExactOutQuote,
    )

    if not isinstance(payload, dict):
        raise ValueError("bad_exact_out_quote")
    amount_out_total = payload.get("amount_out_total")
    amount_in_total = payload.get("amount_in_total")
    legs = payload.get("legs")
    if not isinstance(amount_out_total, int) or isinstance(amount_out_total, bool) or amount_out_total <= 0:
        raise ValueError("bad_amount_out_total")
    if not isinstance(amount_in_total, int) or isinstance(amount_in_total, bool) or amount_in_total <= 0:
        raise ValueError("bad_amount_in_total")
    if not isinstance(legs, list) or not legs:
        raise ValueError("bad_exact_out_legs")

    parsed_legs = []
    for leg in legs:
        if not isinstance(leg, dict):
            raise ValueError("bad_exact_out_leg")
        pool_id = leg.get("pool_id")
        amount_out = leg.get("amount_out")
        amount_in = leg.get("amount_in")
        if not isinstance(pool_id, str) or not pool_id:
            raise ValueError("bad_exact_out_leg_pool_id")
        if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
            raise ValueError("bad_exact_out_leg_amount_out")
        if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
            raise ValueError("bad_exact_out_leg_amount_in")
        parsed_legs.append(
            SplitLegExactOutQuote(
                pool_id=pool_id,
                amount_out=int(amount_out),
                amount_in=int(amount_in),
            )
        )

    return SplitManyPoolsExactOutQuote(
        amount_out_total=int(amount_out_total),
        amount_in_total=int(amount_in_total),
        legs=tuple(parsed_legs),
    )


def projected_path_from_exact_out_quote_payload(payload: object) -> Optional[list[list[object]]]:
    """Project an exact-out quote payload into [[pool_id, amount_out, amount_in], ...].

    Mirrors the closure at ``api_server.py:1575-1597``. Returns ``None`` if
    payload is ``None`` (legacy fall-through behavior).
    """
    if payload is None:
        return None
    if not isinstance(payload, dict):
        raise ValueError("bad_exact_out_quote_payload")
    legs = payload.get("legs")
    if not isinstance(legs, list):
        raise ValueError("bad_exact_out_quote_legs")
    projected: list[list[object]] = []
    for leg in legs:
        if not isinstance(leg, dict):
            raise ValueError("bad_exact_out_quote_leg")
        pool_id = leg.get("pool_id")
        amount_out = leg.get("amount_out")
        amount_in = leg.get("amount_in")
        if not isinstance(pool_id, str) or not pool_id:
            raise ValueError("bad_exact_out_quote_leg_pool_id")
        if not isinstance(amount_out, int) or isinstance(amount_out, bool):
            raise ValueError("bad_exact_out_quote_leg_amount_out")
        if not isinstance(amount_in, int) or isinstance(amount_in, bool):
            raise ValueError("bad_exact_out_quote_leg_amount_in")
        projected.append([pool_id, int(amount_out), int(amount_in)])
    return projected


# ============================================================================
# Step 6: Declarative schema layer for handler input validation.
#
# Replaces the ad-hoc `int_fields = ((name, value, min), ...)` tuple loop
# pattern duplicated across 30+ handlers in dex_dispatch_handlers.py. A
# schema (list of IntFieldSpec / StrFieldSpec / etc) is the single source
# of truth — used both for runtime validation AND OpenAPI/JSON-Schema
# generation in Step 7.
#
# Why stdlib-only (dataclasses) instead of msgspec / Pydantic:
#   - Adding a runtime dependency requires the dependency-approval gate
#     (tools/check_dependency_change_approval.py) and increases TCB.
#   - Validation here is shallow (flat JSON bodies, no nested structures
#     beyond pool lists and integer lists); a 200-line stdlib layer
#     covers every existing pattern without external code.
#   - mypy --strict friendly without plugin gymnastics.
# ============================================================================


@dataclass(frozen=True)
class IntFieldSpec:
    """Declarative spec for an integer JSON-body field.

    Used by ``parse_int_kwargs`` to validate a body and produce a
    ``dict[str, int]`` ready to splat as ``**kwargs`` into a core function.
    Also serves as the source of truth for OpenAPI/JSON-Schema generation:
    ``name``, ``minimum``, ``maximum``, ``default``, ``description`` all
    map directly to JSON-Schema fields.
    """

    name: str
    default: Optional[int] = None  # None means required
    minimum: Optional[int] = None
    maximum: Optional[int] = None
    description: str = ""

    @property
    def required(self) -> bool:
        return self.default is None

    def to_json_schema(self) -> dict[str, Any]:
        """Emit a JSON-Schema fragment for this field (for OpenAPI)."""
        schema: dict[str, Any] = {"type": "integer"}
        if self.minimum is not None:
            schema["minimum"] = self.minimum
        if self.maximum is not None:
            schema["maximum"] = self.maximum
        if self.default is not None:
            schema["default"] = self.default
        if self.description:
            schema["description"] = self.description
        return schema


def parse_int_kwargs(
    obj: Mapping[str, Any],
    specs: Sequence[IntFieldSpec],
) -> dict[str, int]:
    """Validate ``obj`` against ``specs`` and return a ``dict[str, int]``.

    Raises ``BadFieldError(name, reason)`` on the first failure. The error
    field/reason are byte-stable so they can be relied on by tests and by
    the dispatcher's catch-all formatter.

    Behavior matches the existing per-handler ``int_fields`` tuple loop:
      - missing key with default=None → ``BadFieldError(name, "field is required")``
      - missing key with default → uses default
      - bool value (even though Python's bool is int subclass) → rejected
      - non-int type → rejected
      - value below ``minimum`` → rejected
      - value above ``maximum`` → rejected

    The returned dict's key order matches the spec order (Python 3.7+
    dict insertion ordering), so callers can splat it as ``**kwargs`` into
    functions that take positional-or-keyword arguments without reordering
    issues.
    """
    out: dict[str, int] = {}
    for spec in specs:
        if spec.name not in obj:
            if spec.default is None:
                raise BadFieldError(spec.name, "field is required")
            out[spec.name] = spec.default
            continue
        value = obj[spec.name]
        if isinstance(value, bool) or not isinstance(value, int):
            raise BadFieldError(spec.name, "must be an int (bool rejected)")
        if spec.minimum is not None and value < spec.minimum:
            raise BadFieldError(spec.name, f"must be >= {spec.minimum}")
        if spec.maximum is not None and value > spec.maximum:
            raise BadFieldError(spec.name, f"must be <= {spec.maximum}")
        out[spec.name] = value
    return out


@dataclass(frozen=True)
class EndpointSchema:
    """Declarative schema for a single ``/api/dex/*`` endpoint body.

    Carried alongside the handler in the dispatch registry so the OpenAPI
    generator (Step 7) can emit a path + request body schema from a
    single source. The schema is used by handlers at runtime via
    ``parse_int_kwargs``; it's not (yet) used to auto-generate the
    handler signature.
    """

    int_fields: tuple[IntFieldSpec, ...] = ()
    summary: str = ""
    description: str = ""
    # Non-int required fields that handlers validate ad-hoc (parse_pools
    # for ``pools``, ``str(obj.get("asset_in", "")).strip()`` for assets,
    # etc.). Declaring them here lets OpenAPI honestly tell clients these
    # fields are required so generated SDKs do not produce spec-valid
    # bodies that the runtime then rejects.
    requires_pools: bool = False
    requires_assets: bool = False  # asset_in + asset_out
    extra_required: tuple[str, ...] = ()

    def to_request_body_schema(self) -> dict[str, Any]:
        """Emit a JSON-Schema object describing the request body."""
        properties: dict[str, Any] = {}
        required: list[str] = []
        if self.requires_pools:
            properties["pools"] = {
                "type": "array",
                "items": {"type": "object"},
                "minItems": 1,
                "description": "Pool state rows. Validated by parse_pools.",
            }
            required.append("pools")
        if self.requires_assets:
            properties["asset_in"] = {
                "type": "string",
                "minLength": 1,
                "description": "Input asset symbol.",
            }
            properties["asset_out"] = {
                "type": "string",
                "minLength": 1,
                "description": "Output asset symbol (must differ from asset_in).",
            }
            required.extend(["asset_in", "asset_out"])
        for spec in self.int_fields:
            properties[spec.name] = spec.to_json_schema()
            if spec.required:
                required.append(spec.name)
        for name in self.extra_required:
            if name not in properties:
                properties[name] = {"description": "Required by runtime; see handler for type."}
            if name not in required:
                required.append(name)
        schema: dict[str, Any] = {"type": "object", "properties": properties}
        if required:
            schema["required"] = required
        return schema
