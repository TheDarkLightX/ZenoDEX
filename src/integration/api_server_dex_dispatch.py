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

import contextlib
import threading
import time
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Any, Callable, Iterator, Mapping, Optional, Tuple

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
from src.integration import dex_dispatch_handlers as _dex_dispatch_handlers  # noqa: E402, F401

if _REGISTRY_BUILD is None:
    raise RuntimeError("dex endpoint registry build table missing")


def _freeze_registry(
    build: dict[str, DexEndpointSpec],
) -> tuple[Mapping[str, DexEndpointSpec], Callable[[str, DexEndpointSpec], "contextlib.AbstractContextManager[None]"]]:
    """Build the frozen registry view and a test-only mutation hatch.

    The backing dict is closed over by the returned helpers and never
    exposed as a module attribute, so production code cannot bypass the
    ``MappingProxyType`` view. The returned context manager is the only
    documented way to add a synthetic handler for testing; it cleans up
    on exit even if the test body raises.
    """
    backing: dict[str, DexEndpointSpec] = dict(build)
    view: Mapping[str, DexEndpointSpec] = MappingProxyType(backing)

    @contextlib.contextmanager
    def _register_for_test(path: str, spec: DexEndpointSpec) -> Iterator[None]:
        if path in backing:
            raise RuntimeError(f"path already registered: {path}")
        backing[path] = spec
        try:
            yield
        finally:
            backing.pop(path, None)

    return view, _register_for_test


DEX_ENDPOINT_REGISTRY, _register_for_test = _freeze_registry(_REGISTRY_BUILD)
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


# ============================================================================
# Step 8: Per-endpoint dispatch metrics.
#
# Operator-facing observability for the /api/dex/* dispatch path. Tracks
# request count, error count, latency samples (kept to a bounded
# reservoir so p50/p95 stay accurate under steady load without unbounded
# memory), and the most-recent error code per endpoint.
#
# Why in-process counters and not OpenTelemetry/Prometheus:
#   - Adding a metrics SDK is a runtime dependency change requiring
#     the same approval gate as msgspec. Out-of-scope for this turn.
#   - The values are still externally consumable via GET /api/dex/metrics,
#     where an operator's Prometheus exporter / log scraper can pull
#     them. Future migration to a real metrics SDK is a thin shim.
#   - Sufficient for "is the DEX healthy?" — which is the gap we're
#     closing today.
# ============================================================================

_METRICS_LATENCY_RESERVOIR = 512
"""How many latency samples to retain per endpoint for percentile
computation. Bounded so a long-running process doesn't accumulate
unbounded memory. Replacement policy: ring-buffer (oldest replaced
first). At RPS=10, this window is the most recent ~50s."""


@dataclass
class EndpointMetrics:
    """Per-endpoint observability state. Mutable; protected by the
    DispatchMetrics lock for thread-safety under ThreadingHTTPServer."""

    request_count: int = 0
    error_count: int = 0
    """Count of dispatcher catch-all triggers (handler raised an
    unhandled exception). Does NOT include DexEndpointError (those are
    expected 4xx, not server errors) but DOES include BadFieldError
    since those map to 400 'bad_X' codes."""
    latency_samples_ms: list[float] = field(default_factory=list)
    latency_cursor: int = 0  # ring-buffer write position
    most_recent_error_code: Optional[str] = None
    most_recent_error_timestamp_ms: Optional[int] = None

    def record_latency(self, latency_ms: float) -> None:
        """Append a latency sample to the bounded reservoir (ring buffer)."""
        if len(self.latency_samples_ms) < _METRICS_LATENCY_RESERVOIR:
            self.latency_samples_ms.append(latency_ms)
        else:
            self.latency_samples_ms[self.latency_cursor] = latency_ms
            self.latency_cursor = (self.latency_cursor + 1) % _METRICS_LATENCY_RESERVOIR

    def to_public_dict(self) -> dict[str, Any]:
        """Render percentiles + counters as a JSON-friendly dict.

        Computed on read so we don't pay for sorting on every request.
        Empty samples return None for percentile values.
        """
        samples = sorted(self.latency_samples_ms)
        n = len(samples)
        out: dict[str, Any] = {
            "request_count": self.request_count,
            "error_count": self.error_count,
            "sample_count": n,
            "latency_p50_ms": _percentile_or_none(samples, 50, n),
            "latency_p95_ms": _percentile_or_none(samples, 95, n),
            "latency_p99_ms": _percentile_or_none(samples, 99, n),
            "most_recent_error_code": self.most_recent_error_code,
            "most_recent_error_timestamp_ms": self.most_recent_error_timestamp_ms,
        }
        return out


def _percentile_or_none(sorted_samples: list[float], pct: int, n: int) -> Optional[float]:
    """Nearest-rank percentile from a pre-sorted list. None on empty.

    Nearest-rank is what operators expect ("p95 = at most 5% of requests
    were slower than this"). Linear interpolation would be off by a sample.
    """
    if n == 0:
        return None
    if n == 1:
        return sorted_samples[0]
    # bisect-based nearest-rank: ceil(pct/100 * n) - 1
    rank = max(0, min(n - 1, (pct * n + 99) // 100 - 1))
    return sorted_samples[rank]


class DispatchMetrics:
    """Thread-safe per-endpoint metrics for the dispatch path.

    The single global instance ``DISPATCH_METRICS`` is mutated by every
    request and read by ``GET /api/dex/metrics``. Operations are coarse
    locked (single lock for all endpoints) because:
      - Per-endpoint locks add complexity without measurable contention
        win at expected DEX request rates (10s-100s RPS).
      - The lock is held for ~1µs (counter increment + reservoir write).
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._endpoints: dict[str, EndpointMetrics] = {}

    def record_request(
        self,
        path: str,
        *,
        latency_ms: float,
        is_error: bool,
        error_code: Optional[str] = None,
    ) -> None:
        with self._lock:
            ep = self._endpoints.get(path)
            if ep is None:
                ep = EndpointMetrics()
                self._endpoints[path] = ep
            ep.request_count += 1
            ep.record_latency(latency_ms)
            if is_error:
                ep.error_count += 1
                ep.most_recent_error_code = error_code
                ep.most_recent_error_timestamp_ms = int(time.time() * 1000)

    def snapshot(self) -> dict[str, dict[str, Any]]:
        """Atomic snapshot of all endpoints' counters. Safe to JSON-serialize."""
        with self._lock:
            return {
                path: ep.to_public_dict()
                for path, ep in sorted(self._endpoints.items())
            }

    def reset(self) -> None:
        """Wipe all counters. Tests use this for isolation."""
        with self._lock:
            self._endpoints.clear()


DISPATCH_METRICS = DispatchMetrics()
"""Single global instance. Read by ``GET /api/dex/metrics`` and mutated
by every ``dispatch()`` call."""


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


def dispatch(path: str, obj: Mapping[str, Any], ctx: DexRequestContext) -> Optional[DexResponse]:
    """Look up a handler and run it with uniform exception handling.

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

    start_ns = time.perf_counter_ns()
    response, error_code_for_metrics = _run_endpoint_handler(path, spec, obj, ctx)
    latency_ms = (time.perf_counter_ns() - start_ns) / 1_000_000.0

    # Treat status >= 400 as an error for metrics purposes (even if the
    # handler chose to return it directly without raising). Matches what
    # an operator wants: "how many requests came back with an error?"
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


def serve_metrics() -> dict[str, Any]:
    """Render the dispatch metrics as a JSON-serializable dict.

    Served at ``GET /api/dex/metrics``. Shape:
      {
        "metrics": {
          "/api/dex/<endpoint>": {
            "request_count": int,
            "error_count": int,
            "sample_count": int,
            "latency_p50_ms": float | None,
            "latency_p95_ms": float | None,
            "latency_p99_ms": float | None,
            "most_recent_error_code": str | None,
            "most_recent_error_timestamp_ms": int | None,
          },
          ...
        },
        "endpoint_count": int,
        "total_request_count": int,
      }
    """
    endpoints = DISPATCH_METRICS.snapshot()
    return {
        "metrics": endpoints,
        "endpoint_count": len(endpoints),
        "total_request_count": sum(m["request_count"] for m in endpoints.values()),
    }
