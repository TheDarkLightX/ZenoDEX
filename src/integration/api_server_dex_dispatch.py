"""Dispatch registry for ``/api/dex/*`` HTTP endpoints.

Replaces the 84-endpoint, 945-cyclomatic-complexity if-chain inside
``api_server.py::_Handler._maybe_handle_dex_api`` with a frozen
``MappingProxyType`` registry. Each handler is a free function taking a
parsed JSON body plus a ``DexRequestContext`` and returning a
``DexResponse = (status, body)`` tuple. Handlers are migrated incrementally
behind a strangler-fig seam: ``_maybe_handle_dex_api`` looks up the path in
this registry first and falls through to the legacy chain on miss.

Design constraints (locked in PR1):

  * Registry is copied into a ``MappingProxyType`` at module import. No
    mutable backing dict remains reachable after import; parallel test
    isolation depends on this.
  * Handlers receive a pre-parsed JSON object (dict). The dispatcher in
    ``api_server.py`` runs auth + method + JSON-parse + search-limit
    guards before lookup.
  * Handlers must NOT touch ``self`` or the HTTP response stream. They
    return ``(status, body)``; the caller writes the response.
  * ``except Exception`` semantics are preserved: handlers may raise, the
    dispatcher catches and returns a 400 with the endpoint-specific
    error code as legacy did.
  * Imports of functional-core modules stay inside handler bodies (lazy)
    to preserve the existing import-cycle guard.
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Callable, Mapping, Optional, Tuple

from src.integration.api_server_dex_metrics import (
    _METRICS_LATENCY_RESERVOIR as _METRICS_LATENCY_RESERVOIR,
)
from src.integration.api_server_dex_metrics import (
    DISPATCH_METRICS,
)
from src.integration.api_server_dex_metrics import (
    DispatchMetrics as DispatchMetrics,
)
from src.integration.api_server_dex_metrics import (
    EndpointMetrics as EndpointMetrics,
)
from src.integration.api_server_dex_metrics import (
    serve_metrics as serve_metrics,
)

DexResponse = Tuple[int, Mapping[str, Any]]


class DexEndpointError(Exception):
    """Structured error raised by handlers when an early-exit response is needed.

    Handlers raise ``DexEndpointError(400, "bad_assets")`` instead of
    returning ``(400, {"ok": False, "error": "bad_assets"})``. The dispatcher
    converts the exception into the standard response shape, removing the
    boilerplate ``return 400, {...}`` from every validation branch.

    Subclasses ``Exception`` (not ``ValueError``) so ``except Exception`` in
    handlers — should any remain during migration — still catches it but a
    ``DexEndpointError``-specific clause can extract structured fields.
    """

    def __init__(self, status: int, code: str, **details: Any) -> None:
        self.status = status
        self.code = code
        self.details = details
        super().__init__(f"{status} {code}: {details}")

    @property
    def response(self) -> DexResponse:
        body: dict[str, Any] = {"ok": False, "error": self.code}
        body.update(self.details)
        return self.status, body


@dataclass(frozen=True)
class DexRequestContext:
    """Context handlers may need beyond the parsed body.

    ``server`` exposes the HTTP server instance for handlers that legitimately
    read/write server-scoped state (e.g. the active DexState snapshot). New
    handlers should prefer pure-function logic against the body and pull
    from ``server`` only when the legacy handler did so.
    """

    server: Any
    cors_origin: Optional[str]
    raw_body: Optional[bytes]


DexEndpointHandler = Callable[[Mapping[str, Any], DexRequestContext], DexResponse]


@dataclass(frozen=True)
class DexEndpointSpec:
    """Registry entry: handler, catch-all error code, and (optionally) the
    declarative ``EndpointSchema`` used for runtime validation + OpenAPI.

    ``default_error_code`` is the code returned by the dispatcher when the
    handler raises an unexpected exception (anything other than
    ``DexEndpointError`` / ``BadFieldError``). Matches the legacy
    "<endpoint>_error" pattern.

    ``schema`` is the declarative ``EndpointSchema`` carrying the int
    fields the handler validates via ``parse_int_kwargs``. Schemas live
    in ``_dex_api_helpers.py``; we accept ``Any`` here to avoid an
    import cycle (the helpers module doesn't depend on this one).
    Endpoints without a schema (legacy handlers using ad-hoc validation)
    pass ``None`` and are excluded from auto-generated OpenAPI.
    """

    handler: DexEndpointHandler
    default_error_code: str
    schema: Optional[Any] = None


_REGISTRY_BUILD: dict[str, DexEndpointSpec] | None = {}


def _register(
    path: str,
    handler: DexEndpointHandler,
    *,
    default_error_code: str | None = None,
    schema: Optional[Any] = None,
) -> None:
    """Register a handler at ``path``.

    ``default_error_code`` is required for handlers that lean on the
    dispatcher's catch-all (i.e. handlers that have removed their own
    try/except). Handlers that still wrap their own try/except may pass
    ``None`` — the dispatcher's catch-all then never fires for them.

    ``schema`` is an optional ``EndpointSchema`` (from
    ``_dex_api_helpers``) carrying the declarative int-field validation
    rules. Used by ``generate_openapi_fragment`` to emit
    JSON-Schema-backed OpenAPI for the endpoint.
    """
    if not path.startswith("/api/dex/"):
        raise RuntimeError(f"dex endpoint path must start with /api/dex/: {path}")
    frozen_registry = globals().get("DEX_ENDPOINT_REGISTRY")
    if frozen_registry is not None:
        if path in frozen_registry:
            raise RuntimeError(f"duplicate dex endpoint registration: {path}")
        raise RuntimeError("dex endpoint registry is frozen")
    registry = _REGISTRY_BUILD
    if registry is None:
        raise RuntimeError("dex endpoint registry is frozen")
    if path in registry:
        raise RuntimeError(f"duplicate dex endpoint registration: {path}")
    code = default_error_code or _default_error_code_for_path(path)
    registry[path] = DexEndpointSpec(
        handler=handler, default_error_code=code, schema=schema
    )


def _default_error_code_for_path(path: str) -> str:
    """Return the path-suffix-based default error code for ``path``.

    e.g. ``"/api/dex/impact_preview"`` → ``"impact_preview_error"``.
    Exposed so tests can verify the derivation without needing to
    mutate the frozen registry.
    """
    return f"{path.rsplit('/', 1)[-1]}_error"


def _operation_id_for_path(path: str) -> str:
    """Return the OpenAPI operationId for ``path``.

    e.g. ``"/api/dex/impact_preview"`` → ``"handle_impact_preview"``.
    Derived from the path so factory-built handlers (which all share the
    inner function name ``_handler``) don't collide on operationId in
    the generated OpenAPI spec.
    """
    return f"handle_{path.rsplit('/', 1)[-1]}"


# Import handler modules to populate the registry. Each module calls
# ``_register`` at import time. New handler files should be added to this
# import block; do not import them lazily.
from src.integration import (  # noqa: E402
    dex_dispatch_exact_in_route_handlers as _exact_in_route_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_exact_out_advisory_quote_handlers as _exact_out_advisory_quote_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_exact_out_contract_handlers as _exact_out_contract_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_exact_out_default_quote_handlers as _exact_out_default_quote_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_exact_out_guarded_handlers as _exact_out_guarded_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_exact_out_packet_handlers as _exact_out_packet_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_exact_out_verify_handlers as _exact_out_verify_handlers,  # noqa: F401
)
from src.integration import dex_dispatch_proof_mining_handlers as _proof_handlers  # noqa: E402,F401
from src.integration import dex_dispatch_quote_handlers as _quote_handlers  # noqa: E402,F401
from src.integration import dex_dispatch_receipt_handlers as _receipt_handlers  # noqa: E402,F401
from src.integration import (  # noqa: E402
    dex_dispatch_settlement_audit_handlers as _settlement_audit_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_settlement_end_to_end_certificate_handlers as _end_to_end_certificate_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_settlement_endogenous_lp_handlers as _endogenous_lp_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_settlement_value_handlers as _settlement_value_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_settlement_value_packet_handlers as _settlement_value_packet_handlers,  # noqa: F401
)
from src.integration import (  # noqa: E402
    dex_dispatch_settlement_witness_lifecycle_handlers as _settlement_witness_lifecycle_handlers,  # noqa: F401
)
from src.integration import dex_dispatch_slippage_handlers as _slippage_handlers  # noqa: E402,F401

if _REGISTRY_BUILD is None:
    raise RuntimeError("dex endpoint registry build table missing")


DEX_ENDPOINT_REGISTRY: Mapping[str, DexEndpointSpec] = MappingProxyType(dict(_REGISTRY_BUILD))
_REGISTRY_BUILD = None


def lookup(path: str) -> Optional[DexEndpointHandler]:
    """Return the handler registered at ``path`` or ``None`` if absent.

    Returns the bare handler for backwards compatibility with existing test
    code; use ``lookup_spec`` to get the spec including the default error
    code.
    """
    spec = DEX_ENDPOINT_REGISTRY.get(path)
    return spec.handler if spec is not None else None


def lookup_spec(path: str) -> Optional[DexEndpointSpec]:
    """Return the spec registered at ``path`` or ``None`` if absent."""
    return DEX_ENDPOINT_REGISTRY.get(path)


OPENAPI_SPEC_VERSION = "3.1.0"
"""Pinned. Bumping this means re-validating against the new meta-schema."""

DEX_API_VERSION = "0.1.0"
"""Version of the /api/dex/* surface itself. Bump on any breaking change."""


def generate_openapi_document(
    *,
    title: str = "ZenoDex /api/dex/*",
    version: str = DEX_API_VERSION,
    server_url: str | None = None,
) -> dict[str, Any]:
    """Emit a complete OpenAPI 3.1 document for the dispatch registry.

    Covers only endpoints registered with an ``EndpointSchema``; legacy
    handlers without a declarative schema are omitted from the document
    so the published surface never lies about the contract.

    The document is JSON-serializable. Server-side, this is served at
    ``/api/dex/openapi.json`` (wire-up in api_server.py is a follow-up).
    Clients can use it to generate type-safe SDKs.
    """
    paths = generate_openapi_fragment()
    document: dict[str, Any] = {
        "openapi": OPENAPI_SPEC_VERSION,
        "info": {
            "title": title,
            "version": version,
            "description": (
                "Auto-generated OpenAPI for the ZenoDex /api/dex/* dispatch "
                "registry. Only endpoints with a declarative EndpointSchema "
                "are documented here; handlers using ad-hoc validation are "
                "intentionally omitted until their schemas are extracted."
            ),
        },
        "paths": paths,
        "components": {
            "schemas": {
                "ErrorResponse": {
                    "type": "object",
                    "properties": {
                        "ok": {"type": "boolean", "const": False},
                        "error": {
                            "type": "string",
                            "description": "Stable error code (e.g. bad_amount_out_total).",
                        },
                        "details": {"type": "string"},
                    },
                    "required": ["ok", "error"],
                }
            }
        },
    }
    if server_url is not None:
        document["servers"] = [{"url": server_url}]
    return document


def generate_openapi_fragment() -> dict[str, Any]:
    """Emit an OpenAPI 3.1 ``paths`` fragment for every registered endpoint
    that carries an ``EndpointSchema`` via its ``DexEndpointSpec``.

    Step 6 deliverable: the dispatch registry becomes the single source of
    truth for the API surface. Step 7 will wire this into a full OpenAPI
    document with the components, servers, and security schemas.

    Endpoints registered without a schema (the ~60 handlers still using
    ad-hoc validation) are omitted — they'll appear once they're migrated
    to ``parse_int_kwargs(obj, schema.int_fields)`` and re-registered
    with ``schema=...``.
    """
    paths: dict[str, Any] = {}
    # Iterate in sorted path order so the emitted OpenAPI document is
    # deterministic regardless of handler registration order — important
    # for snapshot tests and reproducible-build comparisons.
    for path, spec in sorted(DEX_ENDPOINT_REGISTRY.items()):
        schema = spec.schema
        if schema is None or not hasattr(schema, "to_request_body_schema"):
            continue
        body_schema = schema.to_request_body_schema()
        operation: dict[str, Any] = {
            "operationId": _operation_id_for_path(path),
            "requestBody": {
                "required": True,
                "content": {"application/json": {"schema": body_schema}},
            },
            "responses": {
                "200": {"description": "Success response"},
                "400": {
                    "description": "Validation or processing error",
                    "content": {
                        "application/json": {
                            "schema": {
                                "type": "object",
                                "properties": {
                                    "ok": {"type": "boolean", "const": False},
                                    "error": {"type": "string"},
                                },
                                "required": ["ok", "error"],
                            }
                        }
                    },
                },
            },
        }
        summary = getattr(schema, "summary", "")
        description = getattr(schema, "description", "")
        if summary:
            operation["summary"] = summary
        if description:
            operation["description"] = description
        paths[path] = {"post": operation}
    return paths


def _run_endpoint_handler(
    path: str,
    spec: DexEndpointSpec,
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> tuple[DexResponse, Optional[str]]:
    """Run a handler and convert legacy endpoint exceptions into responses."""
    # Late import keeps the helper module independently importable in tests.
    from src.integration._dex_api_helpers import BadFieldError as _BadFieldError

    try:
        return spec.handler(obj, ctx), None
    except DexEndpointError as exc:
        return exc.response, exc.code
    except _BadFieldError as exc:
        code = f"bad_{exc.field}"
        return (400, {"ok": False, "error": code}), code
    except Exception:
        import sys
        import traceback

        print(
            f"dex dispatch error path={path} code={spec.default_error_code}",
            file=sys.stderr,
        )
        traceback.print_exc(file=sys.stderr)
        return (
            400,
            {"ok": False, "error": spec.default_error_code, "details": "request failed"},
        ), spec.default_error_code


def _returned_error_code(response: DexResponse) -> Optional[str]:
    """Extract the ``error`` code from a handler-returned error body."""
    body = response[1]
    if isinstance(body, Mapping):
        raw_code = body.get("error")
        if isinstance(raw_code, str):
            return raw_code
    return None


def dispatch_endpoint_spec(
    path: str,
    spec: DexEndpointSpec,
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    """Run one explicit immutable endpoint specification.

    Taking the specification as data keeps registry selection separate from
    execution and lets tests exercise the real dispatch behavior without a
    mutable production registry or a test-only mutation hook.
    """
    start_ns = time.perf_counter_ns()
    response, error_code_for_metrics = _run_endpoint_handler(path, spec, obj, ctx)
    latency_ms = (time.perf_counter_ns() - start_ns) / 1_000_000.0

    status = response[0]
    is_error = error_code_for_metrics is not None or status >= 400
    if is_error and error_code_for_metrics is None:
        error_code_for_metrics = _returned_error_code(response)

    DISPATCH_METRICS.record_request(
        path,
        latency_ms=latency_ms,
        is_error=is_error,
        error_code=error_code_for_metrics,
    )
    return response


def dispatch(path: str, obj: Mapping[str, Any], ctx: DexRequestContext) -> Optional[DexResponse]:
    """Look up an immutable handler specification and execute it uniformly.

    Returns ``None`` if no handler is registered (caller should fall through
    to the legacy chain or return 404). Otherwise returns the handler's
    ``DexResponse`` directly, or:

      * ``DexEndpointError`` raised by the handler → its structured
        ``(status, body)`` response.
      * ``BadFieldError`` raised by ``parse_int_kwargs`` / ``int_field``
        / ``optional_int_list_field`` → ``(400, {"ok": False, "error":
        f"bad_{field}"})`` matching the legacy ad-hoc validation shape.
      * Any other ``Exception`` → ``(400, {"ok": False, "error":
        spec.default_error_code, "details": "request failed"})`` matching
        the legacy catch-all.

    The ``BadFieldError`` clause lets handlers use the declarative
    ``parse_int_kwargs`` helper without writing local try/except —
    the dispatcher uniformly converts the validation failure into the
    legacy "bad_{fieldname}" error code.
    """
    spec = DEX_ENDPOINT_REGISTRY.get(path)
    if spec is None:
        return None
    return dispatch_endpoint_spec(path, spec, obj, ctx)
