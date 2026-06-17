"""In-process metrics for the ``/api/dex/*`` dispatch path.

The dispatch layer owns request routing. This module owns operator-facing
observability: bounded latency samples, request/error counters, and the public
``GET /api/dex/metrics`` response shape.
"""

from __future__ import annotations

import threading
import time
from dataclasses import dataclass, field
from typing import Any, Optional

_METRICS_LATENCY_RESERVOIR = 512
"""Latency samples retained per endpoint.

Bounded storage prevents long-running nodes from accumulating unbounded memory.
Replacement policy is a ring buffer: once full, the oldest sample slot is
overwritten. At RPS=10, this window covers the most recent roughly 50 seconds.
"""


@dataclass
class EndpointMetrics:
    """Mutable per-endpoint observability state.

    ``DispatchMetrics`` protects instances with a coarse lock, which is enough
    for ``ThreadingHTTPServer`` request concurrency at expected DEX rates.
    """

    request_count: int = 0
    error_count: int = 0
    latency_samples_ms: list[float] = field(default_factory=list)
    latency_cursor: int = 0
    most_recent_error_code: Optional[str] = None
    most_recent_error_timestamp_ms: Optional[int] = None

    def record_latency(self, latency_ms: float) -> None:
        """Append a latency sample to the bounded ring buffer."""
        if len(self.latency_samples_ms) < _METRICS_LATENCY_RESERVOIR:
            self.latency_samples_ms.append(latency_ms)
            return
        self.latency_samples_ms[self.latency_cursor] = latency_ms
        self.latency_cursor = (self.latency_cursor + 1) % _METRICS_LATENCY_RESERVOIR

    def to_public_dict(self) -> dict[str, Any]:
        """Render counters and nearest-rank percentiles as JSON-friendly data."""
        samples = sorted(self.latency_samples_ms)
        n = len(samples)
        return {
            "request_count": self.request_count,
            "error_count": self.error_count,
            "sample_count": n,
            "latency_p50_ms": _percentile_or_none(samples, 50, n),
            "latency_p95_ms": _percentile_or_none(samples, 95, n),
            "latency_p99_ms": _percentile_or_none(samples, 99, n),
            "most_recent_error_code": self.most_recent_error_code,
            "most_recent_error_timestamp_ms": self.most_recent_error_timestamp_ms,
        }


def _percentile_or_none(sorted_samples: list[float], pct: int, n: int) -> Optional[float]:
    """Nearest-rank percentile from a pre-sorted list. ``None`` on empty."""
    if n == 0:
        return None
    if n == 1:
        return sorted_samples[0]
    rank = max(0, min(n - 1, (pct * n + 99) // 100 - 1))
    return sorted_samples[rank]


class DispatchMetrics:
    """Thread-safe per-endpoint metrics for the dispatch path."""

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
        """Atomic snapshot of all endpoint counters."""
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
"""Single process-local metrics instance for the DEX dispatch path."""


def serve_metrics() -> dict[str, Any]:
    """Render the dispatch metrics as a JSON-serializable dict."""
    endpoints = DISPATCH_METRICS.snapshot()
    return {
        "metrics": endpoints,
        "endpoint_count": len(endpoints),
        "total_request_count": sum(m["request_count"] for m in endpoints.values()),
    }
