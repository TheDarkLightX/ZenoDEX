"""
Minimal HTTP API server for ZenoDEX container deployments.

This server is intentionally small and dependency-free (stdlib only).
It exists to support:
- container health checks
- a future thin REST surface (optional)

Security posture:
- Default-deny CORS (no wildcard by default)
- Basic rate limiting (per-IP, token bucket)
- Tight request parsing and bounded request sizes
- Optional bearer-token auth for demo/dev routes (DEMO_API_TOKEN)
"""

from __future__ import annotations

import json
import hmac
import os
import threading
import time
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Optional, Sequence, Set


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        v = int(raw.strip())
    except Exception:
        return int(default)
    if v < lo:
        return int(lo)
    if v > hi:
        return int(hi)
    return int(v)


def _env_str(name: str, default: str) -> str:
    raw = os.environ.get(name)
    if raw is None:
        return default
    v = raw.strip()
    return v if v else default


def _parse_cors_origins(value: str) -> Set[str]:
    """
    Parse CORS origins list. Supports comma-separated values.

    Security: default should be empty (deny CORS). We explicitly treat '*'
    as unsafe and ignore it.
    """
    out: Set[str] = set()
    s = (value or "").strip()
    if not s:
        return out
    for item in s.split(","):
        origin = item.strip()
        if not origin:
            continue
        if origin == "*":
            # Explicitly refuse wildcard; force operators to list trusted origins.
            continue
        out.add(origin)
    return out


def _is_loopback_host(host: str) -> bool:
    h = (host or "").strip().lower()
    return h in ("127.0.0.1", "localhost", "::1")


@dataclass
class RateLimitBucket:
    tokens: float
    updated_at: float


class TokenBucketRateLimiter:
    """
    Per-IP token bucket.

    Target complexity: O(1) per request.
    """

    def __init__(self, *, rpm: int, max_buckets: int = 10_000) -> None:
        self._rpm = int(max(0, rpm))
        self._capacity = float(max(1, rpm)) if rpm > 0 else 0.0
        self._refill_per_s = float(rpm) / 60.0 if rpm > 0 else 0.0
        self._max_buckets = int(max(1, max_buckets))
        self._buckets: dict[str, RateLimitBucket] = {}
        self._lock = threading.Lock()

    def allow(self, key: str) -> bool:
        if self._rpm <= 0:
            return True
        now = time.time()
        with self._lock:
            b = self._buckets.get(key)
            if b is None:
                # Prevent unbounded growth if the server is exposed publicly.
                if len(self._buckets) >= self._max_buckets:
                    return False
                self._buckets[key] = RateLimitBucket(tokens=self._capacity - 1.0, updated_at=now)
                return True
            dt = max(0.0, now - float(b.updated_at))
            b.tokens = min(self._capacity, float(b.tokens) + dt * self._refill_per_s)
            b.updated_at = now
            if b.tokens >= 1.0:
                b.tokens -= 1.0
                return True
            return False


class _Handler(BaseHTTPRequestHandler):
    server_version = "ZenoDEXApi/1"

    # Bound request line / headers to avoid memory abuse.
    # BaseHTTPRequestHandler uses this to cap header size.
    # https://docs.python.org/3/library/http.server.html
    max_requestline = 8192
    max_headers = 100

    def _client_ip(self) -> str:
        # Trust boundary: we do NOT trust X-Forwarded-For in-container.
        host = getattr(self.client_address, "__iter__", None)
        if host is None:
            return "unknown"
        return str(self.client_address[0])

    def _cors_origin(self) -> Optional[str]:
        origin = self.headers.get("Origin")
        if not isinstance(origin, str) or not origin:
            return None
        return origin

    def _write_json(self, status: int, obj: object, *, cors_origin: Optional[str]) -> None:
        body = json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        self.send_response(int(status))
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        if int(status) == 401:
            # Hint for clients and intermediaries (even though we don't use Basic auth).
            self.send_header("WWW-Authenticate", "Bearer")
        self.send_header("Content-Length", str(len(body)))
        if cors_origin is not None:
            self.send_header("Access-Control-Allow-Origin", cors_origin)
            self.send_header("Vary", "Origin")
        self.end_headers()
        self.wfile.write(body)

    def _maybe_rate_limit(self) -> bool:
        limiter: TokenBucketRateLimiter = getattr(self.server, "rate_limiter")  # type: ignore[attr-defined]
        return limiter.allow(self._client_ip())

    def _allowed_cors_origin_or_none(self) -> Optional[str]:
        allowed: Set[str] = getattr(self.server, "cors_origins")  # type: ignore[attr-defined]
        origin = self._cors_origin()
        if origin is None:
            return None
        return origin if origin in allowed else None

    def _demo_auth_ok(self) -> bool:
        """Optional bearer token auth for demo/dev routes.

        If no token is configured, auth is not enforced.
        """
        token = getattr(self.server, "demo_api_token", "")  # type: ignore[attr-defined]
        if not isinstance(token, str) or not token:
            return True
        auth = self.headers.get("Authorization")
        if not isinstance(auth, str) or not auth:
            return False
        parts = auth.strip().split()
        if len(parts) != 2 or parts[0].lower() != "bearer":
            return False
        return hmac.compare_digest(parts[1], token)

    def _read_raw_body_with_error(
        self, max_bytes: int = 65536
    ) -> tuple[Optional[bytes], Optional[tuple[int, str]]]:
        """Read raw request body bytes (bounded), returning (body, (status, error)) on failure."""
        length_str = self.headers.get("Content-Length")
        if length_str is None:
            return None, None
        try:
            length = int(length_str)
        except (ValueError, TypeError):
            return None, (400, "invalid_content_length")
        if length <= 0:
            return b"", None
        if length > max_bytes:
            # Refuse to read an oversized body; close the connection so the client can't
            # keep streaming bytes after we respond.
            self.close_connection = True
            return None, (413, "body_too_large")
        return self.rfile.read(length), None

    def _read_json_body(self, max_bytes: int = 65536) -> Optional[dict[str, Any]]:
        """Read and parse a JSON request body, or None on error."""
        length_str = self.headers.get("Content-Length")
        if length_str is None:
            return None
        try:
            length = int(length_str)
        except (ValueError, TypeError):
            return None
        if length <= 0 or length > max_bytes:
            return None
        raw = self.rfile.read(length)
        try:
            obj = json.loads(raw)
        except (json.JSONDecodeError, UnicodeDecodeError):
            return None
        if not isinstance(obj, dict):
            return None
        return obj

    def _perps_state(self) -> Any:
        """Get the current PerpsState from the server (may be None)."""
        return getattr(self.server, "perps_state", None)

    def _maybe_handle_perps_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/perps/"):
            return False
        if not getattr(self.server, "perps_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.perps_api import handle_perps_request

        status, resp = handle_perps_request(method, path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_zusd_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/zusd/"):
            return False
        if not getattr(self.server, "zusd_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.zusd_api import handle_zusd_request

        status, resp = handle_zusd_request(method, path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def do_OPTIONS(self) -> None:  # noqa: N802
        cors_origin = self._allowed_cors_origin_or_none()
        if cors_origin is None:
            self.send_response(204)
            self.end_headers()
            return
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", cors_origin)
        self.send_header("Access-Control-Allow-Methods", "GET,POST,OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, Authorization")
        self.send_header("Access-Control-Max-Age", "600")
        self.send_header("Vary", "Origin")
        self.end_headers()

    def do_GET(self) -> None:  # noqa: N802
        cors_origin = self._allowed_cors_origin_or_none()
        if not self._maybe_rate_limit():
            self._write_json(429, {"ok": False, "error": "rate_limited"}, cors_origin=cors_origin)
            return

        path = (self.path or "").split("?", 1)[0]

        if path == "/health":
            self._write_json(200, {"status": "healthy", "service": "zenodex-api"}, cors_origin=cors_origin)
            return

        if path == "/version":
            self._write_json(
                200,
                {
                    "service": "zenodex-api",
                    "python": os.environ.get("PYTHON_VERSION", ""),
                },
                cors_origin=cors_origin,
            )
            return

        if path == "/api/confidential/status":
            status = getattr(self.server, "confidential_feature_status", None)  # type: ignore[attr-defined]
            if not isinstance(status, dict):
                from src.integration.confidential_feature_status import load_confidential_feature_status_from_env  # pylint: disable=import-outside-toplevel

                status = load_confidential_feature_status_from_env().to_public_dict()
            self._write_json(200, {"ok": True, "status": status}, cors_origin=cors_origin)
            return

        # Demo/dev routes (gated by env vars in main()).
        if self._maybe_handle_perps_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_zusd_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return

        self._write_json(404, {"ok": False, "error": "not_found"}, cors_origin=cors_origin)

    def do_POST(self) -> None:  # noqa: N802
        cors_origin = self._allowed_cors_origin_or_none()
        if not self._maybe_rate_limit():
            self._write_json(429, {"ok": False, "error": "rate_limited"}, cors_origin=cors_origin)
            return

        path = (self.path or "").split("?", 1)[0]

        raw_body = None
        if path.startswith("/api/perps/") or path.startswith("/api/zusd/"):
            ctype = (self.headers.get("Content-Type") or "").split(";", 1)[0].strip().lower()
            if ctype and ctype != "application/json":
                self._write_json(415, {"ok": False, "error": "unsupported_media_type"}, cors_origin=cors_origin)
                return
            raw_body, err = self._read_raw_body_with_error()
            if err is not None:
                status, code = err
                self._write_json(int(status), {"ok": False, "error": str(code)}, cors_origin=cors_origin)
                return
        if self._maybe_handle_perps_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_zusd_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return

        self._write_json(404, {"ok": False, "error": "not_found"}, cors_origin=cors_origin)

    def log_message(self, fmt: str, *args: object) -> None:
        # Keep logs minimal and deterministic (avoid leaking headers/query strings).
        # Default implementation prints client IP + full request line.
        msg = fmt % args if args else fmt
        safe_path = (self.path or "").split("?", 1)[0]
        safe_path = "".join(ch if 0x20 <= ord(ch) < 0x7F else "?" for ch in safe_path)
        if len(safe_path) > 2048:
            safe_path = safe_path[:2048] + "..."
        line = f"{self.command} {safe_path} => {msg}"
        print(line)


def main(argv: Optional[Sequence[str]] = None) -> int:
    _ = argv
    host = _env_str("API_HOST", "127.0.0.1")
    port = _env_int("API_PORT", 8000, lo=1, hi=65535)
    cors_origins = _parse_cors_origins(_env_str("CORS_ORIGINS", ""))
    rpm = _env_int("RATE_LIMIT_RPM", 600, lo=0, hi=1_000_000)
    max_buckets = _env_int("RATE_LIMIT_MAX_BUCKETS", 10_000, lo=1, hi=1_000_000)

    perps_enabled = _env_str("PERPS_API_ENABLED", "false").lower() in ("1", "true", "yes")
    zusd_enabled = _env_str("ZUSD_API_ENABLED", "false").lower() in ("1", "true", "yes")
    demo_api_token = _env_str("DEMO_API_TOKEN", "")
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env  # pylint: disable=import-outside-toplevel
    confidential_feature_status = load_confidential_feature_status_from_env().to_public_dict()

    if (perps_enabled or zusd_enabled) and (not demo_api_token) and (not _is_loopback_host(host)):
        print(
            "Refusing to start: demo APIs enabled on non-loopback host without DEMO_API_TOKEN "
            f"(host={host!r}, perps_api={perps_enabled}, zusd_api={zusd_enabled})"
        )
        return 2

    httpd = ThreadingHTTPServer((host, port), _Handler)
    # Attach config to server instance (used by handler).
    httpd.cors_origins = cors_origins  # type: ignore[attr-defined]
    httpd.rate_limiter = TokenBucketRateLimiter(rpm=rpm, max_buckets=max_buckets)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = perps_enabled  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = zusd_enabled  # type: ignore[attr-defined]
    httpd.demo_api_token = demo_api_token  # type: ignore[attr-defined]
    httpd.confidential_feature_status = confidential_feature_status  # type: ignore[attr-defined]

    print(
        f"zenodex-api listening on http://{host}:{port} "
        f"(cors_origins={sorted(cors_origins)}, rpm={rpm}, max_buckets={max_buckets}, "
        f"perps_api={perps_enabled}, zusd_api={zusd_enabled}, dex_api={dex_enabled}, "
        f"confidential_stage={confidential_feature_status.get('stage')}, demo_api_token_set={bool(demo_api_token)})"
    )
    httpd.serve_forever(poll_interval=0.25)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
