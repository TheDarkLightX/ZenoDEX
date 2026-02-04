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
"""

from __future__ import annotations

import json
import os
import time
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Optional, Sequence, Set


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


@dataclass
class RateLimitBucket:
    tokens: float
    updated_at: float


class TokenBucketRateLimiter:
    """
    Per-IP token bucket.

    Target complexity: O(1) per request.
    """

    def __init__(self, *, rpm: int) -> None:
        self._rpm = int(max(0, rpm))
        self._capacity = float(max(1, rpm)) if rpm > 0 else 0.0
        self._refill_per_s = float(rpm) / 60.0 if rpm > 0 else 0.0
        self._buckets: dict[str, RateLimitBucket] = {}

    def allow(self, key: str) -> bool:
        if self._rpm <= 0:
            return True
        now = time.time()
        b = self._buckets.get(key)
        if b is None:
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

    def do_OPTIONS(self) -> None:  # noqa: N802
        cors_origin = self._allowed_cors_origin_or_none()
        if cors_origin is None:
            self.send_response(204)
            self.end_headers()
            return
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", cors_origin)
        self.send_header("Access-Control-Allow-Methods", "GET,OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Max-Age", "600")
        self.send_header("Vary", "Origin")
        self.end_headers()

    def do_GET(self) -> None:  # noqa: N802
        if not self._maybe_rate_limit():
            self._write_json(429, {"ok": False, "error": "rate_limited"}, cors_origin=None)
            return

        cors_origin = self._allowed_cors_origin_or_none()
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

        self._write_json(404, {"ok": False, "error": "not_found"}, cors_origin=cors_origin)

    def log_message(self, fmt: str, *args: object) -> None:
        # Keep logs minimal and deterministic (avoid leaking headers/query strings).
        # Default implementation prints client IP + full request line.
        msg = fmt % args if args else fmt
        line = f"{self.command} {self.path.split('?', 1)[0]} => {msg}"
        print(line)


def main(argv: Optional[Sequence[str]] = None) -> int:
    _ = argv
    host = _env_str("API_HOST", "127.0.0.1")
    port = _env_int("API_PORT", 8000, lo=1, hi=65535)
    cors_origins = _parse_cors_origins(_env_str("CORS_ORIGINS", ""))
    rpm = _env_int("RATE_LIMIT_RPM", 600, lo=0, hi=1_000_000)

    httpd = ThreadingHTTPServer((host, port), _Handler)
    # Attach config to server instance (used by handler).
    httpd.cors_origins = cors_origins  # type: ignore[attr-defined]
    httpd.rate_limiter = TokenBucketRateLimiter(rpm=rpm)  # type: ignore[attr-defined]

    print(f"zenodex-api listening on http://{host}:{port} (cors_origins={sorted(cors_origins)}, rpm={rpm})")
    httpd.serve_forever(poll_interval=0.25)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

