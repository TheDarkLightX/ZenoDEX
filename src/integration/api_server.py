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

    def _maybe_handle_dex_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/dex/"):
            return False
        if not getattr(self.server, "dex_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        if method != "POST":
            self._write_json(405, {"ok": False, "error": "method_not_allowed"}, cors_origin=cors_origin)
            return True
        if raw_body is None:
            self._write_json(400, {"ok": False, "error": "missing_body"}, cors_origin=cors_origin)
            return True

        try:
            obj = json.loads(raw_body)
        except Exception:
            self._write_json(400, {"ok": False, "error": "bad_json"}, cors_origin=cors_origin)
            return True
        if not isinstance(obj, dict):
            self._write_json(400, {"ok": False, "error": "bad_body"}, cors_origin=cors_origin)
            return True

        if path == "/api/dex/impact_preview":
            try:
                from src.core.price_impact_preview import price_impact_preview  # pylint: disable=import-outside-toplevel

                reserve_in = int(obj.get("reserve_in", 0))
                reserve_out = int(obj.get("reserve_out", 0))
                amount_in = int(obj.get("amount_in", 0))
                fee_bps = int(obj.get("fee_bps", 0))
                pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
                confidence_bps = int(obj.get("confidence_bps", 9500))

                preview = price_impact_preview(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=amount_in,
                    fee_bps=fee_bps,
                    pending_volume_same_direction=pending_same_dir,
                    confidence_bps=confidence_bps,
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "preview": {
                            "amount_out_isolated": int(preview.amount_out_isolated),
                            "fee_amount": int(preview.fee_amount),
                            "price_impact_bps": int(preview.price_impact_bps),
                            "effective_price_e8": int(preview.effective_price_e8),
                            "spot_price_e8": int(preview.spot_price_e8),
                            "amount_out_best_case": int(preview.amount_out_best_case),
                            "amount_out_worst_case": int(preview.amount_out_worst_case),
                            "recommended_min_out": int(preview.recommended_min_out),
                            "pending_volume_same_direction": int(preview.pending_volume_same_direction),
                            "confidence_bps": int(preview.confidence_bps),
                            "pending_volume_at_confidence": int(preview.pending_volume_at_confidence),
                            "amount_out_at_confidence": int(preview.amount_out_at_confidence),
                        },
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "impact_preview_error", "details": str(exc)[:200]},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/slippage_advice":
            try:
                from src.core.slippage_advisor import (  # pylint: disable=import-outside-toplevel
                    slippage_advice_exact_in_cpmm,
                )
                from src.core.pokayoke_swap_guardrails import (  # pylint: disable=import-outside-toplevel
                    SwapGuardrailContext,
                    decide_swap_guardrails,
                )

                reserve_in = int(obj.get("reserve_in", 0))
                reserve_out = int(obj.get("reserve_out", 0))
                amount_in = int(obj.get("amount_in", 0))
                fee_bps = int(obj.get("fee_bps", 0))
                pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
                confidence_bps = int(obj.get("confidence_bps", 9500))
                max_attacker_amount_in = int(obj.get("max_attacker_amount_in", 5000))
                user_slippage_bps_raw = obj.get("user_slippage_bps", None)
                user_slippage_bps: int | None
                if user_slippage_bps_raw is None:
                    user_slippage_bps = None
                else:
                    user_slippage_bps = int(user_slippage_bps_raw)

                raw_opts = obj.get("slippage_options_bps")
                if isinstance(raw_opts, list):
                    slippage_options_bps = []
                    for x in raw_opts:
                        try:
                            slippage_options_bps.append(int(x))
                        except Exception:
                            continue
                else:
                    slippage_options_bps = None

                advice = slippage_advice_exact_in_cpmm(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    fee_bps=fee_bps,
                    amount_in=amount_in,
                    pending_volume_same_direction=pending_same_dir,
                    confidence_bps=confidence_bps,
                    slippage_options_bps=slippage_options_bps,
                    max_attacker_amount_in=max_attacker_amount_in,
                )

                pokayoke = None
                if user_slippage_bps is not None:
                    ctx = SwapGuardrailContext(
                        price_impact_bps=int(advice.price_impact_bps),
                        slippage_advice_status=str(advice.status),
                        required_slippage_bps=int(advice.required_slippage_bps),
                        recommended_slippage_bps_revert_safe=(
                            int(advice.recommended_slippage_bps_revert_safe)
                            if advice.recommended_slippage_bps_revert_safe is not None
                            else None
                        ),
                        recommended_slippage_bps_mev_safe=(
                            int(advice.recommended_slippage_bps_mev_safe)
                            if advice.recommended_slippage_bps_mev_safe is not None
                            else None
                        ),
                        recommended_slippage_bps=(
                            int(advice.recommended_slippage_bps) if advice.recommended_slippage_bps is not None else None
                        ),
                    )
                    decision = decide_swap_guardrails(ctx=ctx, user_slippage_bps=int(user_slippage_bps))
                    pokayoke = {
                        "action": str(decision.action),
                        "reasons": list(decision.reasons),
                        "messages": list(decision.messages),
                        "typed_confirm_phrase": decision.typed_confirm_phrase,
                    }
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "advice": {
                            "best_amount_out": int(advice.best_amount_out),
                            "price_impact_bps": int(advice.price_impact_bps),
                            "amount_out_at_confidence": int(advice.amount_out_at_confidence),
                            "pending_volume_at_confidence": int(advice.pending_volume_at_confidence),
                            "confidence_bps": int(advice.confidence_bps),
                            "required_slippage_bps": int(advice.required_slippage_bps),
                            "recommended_slippage_bps_revert_safe": (
                                int(advice.recommended_slippage_bps_revert_safe)
                                if advice.recommended_slippage_bps_revert_safe is not None
                                else None
                            ),
                            "recommended_slippage_bps_mev_safe": (
                                int(advice.recommended_slippage_bps_mev_safe)
                                if advice.recommended_slippage_bps_mev_safe is not None
                                else None
                            ),
                            "recommended_slippage_bps": (
                                int(advice.recommended_slippage_bps)
                                if advice.recommended_slippage_bps is not None
                                else None
                            ),
                            "status": str(advice.status),
                            "pokayoke": pokayoke,
                            "options": [
                                {
                                    "slippage_bps": int(o.slippage_bps),
                                    "min_amount_out": int(o.min_amount_out),
                                    "is_revert_safe_at_confidence": bool(o.is_revert_safe_at_confidence),
                                    "sandwich_status": str(o.sandwich_status),
                                    "sandwich_max_profit": int(o.sandwich_max_profit),
                                    "sandwich_attacker_amount_in": int(o.sandwich_attacker_amount_in),
                                    "sandwich_victim_amount_out": int(o.sandwich_victim_amount_out),
                                    "sandwich_scanned_max_attacker_amount_in": int(o.sandwich_scanned_max_attacker_amount_in),
                                }
                                for o in advice.options
                            ],
                        },
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "slippage_advice_error", "details": str(exc)[:200]},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/pokayoke_swap_suggest":
            try:
                from src.core.pokayoke_swap_suggest import (  # pylint: disable=import-outside-toplevel
                    suggest_amount_in_for_impact_lt_bps,
                    suggest_amount_in_for_required_slippage_le_bps,
                )

                reserve_in = int(obj.get("reserve_in", 0))
                reserve_out = int(obj.get("reserve_out", 0))
                amount_in = int(obj.get("amount_in", 0))
                fee_bps = int(obj.get("fee_bps", 0))
                pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
                confidence_bps = int(obj.get("confidence_bps", 9500))

                user_slippage_bps_raw = obj.get("user_slippage_bps", None)
                user_slippage_bps: int | None
                if user_slippage_bps_raw is None:
                    user_slippage_bps = None
                else:
                    user_slippage_bps = int(user_slippage_bps_raw)

                raw_opts = obj.get("slippage_options_bps")
                opts: list[int] = []
                if isinstance(raw_opts, list):
                    for x in raw_opts:
                        try:
                            v = int(x)
                        except Exception:
                            continue
                        if v < 0 or v > 10_000:
                            continue
                        opts.append(int(v))
                max_opt = max(opts) if opts else None

                impact_5 = suggest_amount_in_for_impact_lt_bps(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    fee_bps=fee_bps,
                    amount_in=amount_in,
                    target_impact_bps=500,
                    window=256,
                )
                impact_1 = suggest_amount_in_for_impact_lt_bps(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    fee_bps=fee_bps,
                    amount_in=amount_in,
                    target_impact_bps=100,
                    window=256,
                )

                req_user = (
                    suggest_amount_in_for_required_slippage_le_bps(
                        reserve_in=reserve_in,
                        reserve_out=reserve_out,
                        fee_bps=fee_bps,
                        amount_in=amount_in,
                        pending_volume_same_direction=pending_same_dir,
                        confidence_bps=confidence_bps,
                        target_required_slippage_bps=int(user_slippage_bps),
                        window=256,
                    )
                    if user_slippage_bps is not None
                    else None
                )
                req_max_opt = (
                    suggest_amount_in_for_required_slippage_le_bps(
                        reserve_in=reserve_in,
                        reserve_out=reserve_out,
                        fee_bps=fee_bps,
                        amount_in=amount_in,
                        pending_volume_same_direction=pending_same_dir,
                        confidence_bps=confidence_bps,
                        target_required_slippage_bps=int(max_opt),
                        window=256,
                    )
                    if max_opt is not None
                    else None
                )

                def _as_obj(sugg):
                    if sugg is None:
                        return None
                    return {
                        "kind": str(sugg.kind),
                        "target_bps": int(sugg.target_bps),
                        "suggested_amount_in": int(sugg.suggested_amount_in) if sugg.suggested_amount_in is not None else None,
                        "status": str(sugg.status),
                        "eval_count": int(sugg.eval_count),
                        "baseline_value_bps": int(sugg.baseline_value_bps),
                        "suggested_value_bps": int(sugg.suggested_value_bps) if sugg.suggested_value_bps is not None else None,
                    }

                self._write_json(
                    200,
                    {
                        "ok": True,
                        "suggestions": {
                            "impact_lt_500_bps": _as_obj(impact_5),
                            "impact_lt_100_bps": _as_obj(impact_1),
                            "required_slippage_le_user_bps": _as_obj(req_user),
                            "required_slippage_le_max_option_bps": _as_obj(req_max_opt),
                        },
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "pokayoke_swap_suggest_error", "details": str(exc)[:200]},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/pokayoke_swap_suggest_heavy":
            try:
                from src.core.pokayoke_swap_suggest import (  # pylint: disable=import-outside-toplevel
                    suggest_amount_in_exact_in_cpmm,
                )

                reserve_in = int(obj.get("reserve_in", 0))
                reserve_out = int(obj.get("reserve_out", 0))
                amount_in = int(obj.get("amount_in", 0))
                fee_bps = int(obj.get("fee_bps", 0))
                pending_same_dir = int(obj.get("pending_volume_same_direction", 0))
                confidence_bps = int(obj.get("confidence_bps", 9500))

                user_slippage_bps_raw = obj.get("user_slippage_bps", None)
                if user_slippage_bps_raw is None:
                    raise ValueError("user_slippage_bps is required")
                user_slippage_bps = int(user_slippage_bps_raw)

                raw_opts = obj.get("slippage_options_bps")
                opts: list[int] | None
                if isinstance(raw_opts, list):
                    opts = []
                    for x in raw_opts:
                        try:
                            v = int(x)
                        except Exception:
                            continue
                        if v < 0 or v > 10_000:
                            continue
                        opts.append(int(v))
                else:
                    opts = None

                max_attacker_amount_in_raw = obj.get("max_attacker_amount_in", 2000)
                max_attacker_amount_in = int(max_attacker_amount_in_raw)
                # Hard cap to avoid accidental runaway scans on the API.
                if max_attacker_amount_in < 0 or max_attacker_amount_in > 50_000:
                    raise ValueError("max_attacker_amount_in must be in [0, 50_000]")

                max_evals_raw = obj.get("max_evals", 16)
                max_evals = int(max_evals_raw)
                if max_evals <= 0 or max_evals > 64:
                    raise ValueError("max_evals must be in [1, 64]")

                raw_targets = obj.get("target_actions")
                targets: tuple[str, ...]
                if isinstance(raw_targets, list):
                    cleaned: list[str] = []
                    for x in raw_targets:
                        s = str(x or "").strip().lower()
                        if s in {"confirm", "allow"} and s not in cleaned:
                            cleaned.append(s)
                    targets = tuple(cleaned) if cleaned else ("confirm", "allow")
                else:
                    targets = ("confirm", "allow")

                rows = suggest_amount_in_exact_in_cpmm(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    fee_bps=fee_bps,
                    amount_in=amount_in,
                    pending_volume_same_direction=pending_same_dir,
                    confidence_bps=confidence_bps,
                    slippage_options_bps=opts,
                    max_attacker_amount_in=max_attacker_amount_in,
                    user_slippage_bps=user_slippage_bps,
                    max_evals=max_evals,
                    target_actions=targets,
                )

                def _as_obj(sugg):
                    return {
                        "target_action": str(sugg.target_action),
                        "suggested_amount_in": int(sugg.suggested_amount_in) if sugg.suggested_amount_in is not None else None,
                        "status": str(sugg.status),
                        "eval_count": int(sugg.eval_count),
                        "baseline_action": str(sugg.baseline_action),
                        "suggested_action": str(sugg.suggested_action) if sugg.suggested_action is not None else None,
                        "baseline_reasons": [str(x) for x in (sugg.baseline_reasons or ())],
                        "suggested_reasons": [str(x) for x in (sugg.suggested_reasons or ())] if sugg.suggested_reasons is not None else None,
                    }

                self._write_json(
                    200,
                    {"ok": True, "suggestions": [_as_obj(s) for s in rows]},
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "pokayoke_swap_suggest_heavy_error", "details": str(exc)[:200]},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/proof_mining_status":
            claim_artifact = obj.get("claim")
            chain_balances = obj.get("chain_balances", {})
            tx_sender_pubkey = str(obj.get("tx_sender_pubkey", ""))
            expected_proposal_hash = str(obj.get("expected_proposal_hash", ""))
            app_state_json = obj.get("app_state_json", "")
            if not isinstance(claim_artifact, dict):
                self._write_json(400, {"ok": False, "error": "bad_claim"}, cors_origin=cors_origin)
                return True
            if not isinstance(chain_balances, dict):
                self._write_json(400, {"ok": False, "error": "bad_chain_balances"}, cors_origin=cors_origin)
                return True
            if not isinstance(app_state_json, str):
                self._write_json(400, {"ok": False, "error": "bad_app_state_json"}, cors_origin=cors_origin)
                return True
            if not tx_sender_pubkey:
                self._write_json(400, {"ok": False, "error": "missing_tx_sender_pubkey"}, cors_origin=cors_origin)
                return True
            if not expected_proposal_hash:
                self._write_json(400, {"ok": False, "error": "missing_expected_proposal_hash"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.proof_mining_claimability import (  # pylint: disable=import-outside-toplevel
                    evaluate_proof_mining_claimability,
                )

                reward_pool_pubkey = os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip() or None
                status = evaluate_proof_mining_claimability(
                    reward_pool_pubkey=reward_pool_pubkey,
                    app_state_json=app_state_json,
                    chain_balances=chain_balances,
                    claim_artifact=claim_artifact,
                    tx_sender_pubkey=tx_sender_pubkey,
                    expected_proposal_hash=expected_proposal_hash,
                )
                self._write_json(200, {"ok": True, "status": status.to_public_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "proof_mining_status_error", "details": str(exc)[:200]},
                    cors_origin=cors_origin,
                )
                return True

        def _parse_pools() -> dict[str, Any]:
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
                except Exception as exc:
                    raise ValueError(f"bad pool status: {st_raw}") from exc
                pools_by_id[pid] = PoolState(
                    pool_id=pid,
                    asset0=str(row.get("asset0", "")),
                    asset1=str(row.get("asset1", "")),
                    reserve0=int(row.get("reserve0", 0)),
                    reserve1=int(row.get("reserve1", 0)),
                    fee_bps=int(row.get("fee_bps", 0)),
                    lp_supply=int(row.get("lp_supply", 1)),
                    status=st,
                    created_at=int(row.get("created_at", 0)),
                    curve_tag=str(row.get("curve_tag", "CPMM")),
                    curve_params=row.get("curve_params", ""),
                )
            return pools_by_id

        def _quote_to_dict(q: object) -> dict[str, object]:
            # Minimal JSON shape for UI consumption.
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

        if path == "/api/dex/quote":
            kind = str(obj.get("kind", "")).strip().lower()
            if kind not in {"exact_in", "exact_out"}:
                self._write_json(400, {"ok": False, "error": "bad_kind"}, cors_origin=cors_origin)
                return True
            routing_mode_req = str(obj.get("routing_mode", "exact")).strip().lower()
            if routing_mode_req not in {"exact", "fast_v1"}:
                self._write_json(400, {"ok": False, "error": "bad_routing_mode"}, cors_origin=cors_origin)
                return True
            asset_in = str(obj.get("asset_in", "")).strip()
            asset_out = str(obj.get("asset_out", "")).strip()
            if not asset_in or not asset_out or asset_in == asset_out:
                self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                return True
            try:
                pools_by_id = _parse_pools()
                from src.core.quote_receipts import make_route_quote_receipt  # pylint: disable=import-outside-toplevel
                from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop  # pylint: disable=import-outside-toplevel

                routing_mode_used = str(routing_mode_req)
                if kind == "exact_in":
                    amt = int(obj.get("amount_in", 0))
                    if routing_mode_req == "fast_v1":
                        # Advisory-only fast path: float ranking + exact integer replay per-hop.
                        # Safety: fail-closed to the exact deterministic router on any error.
                        try:
                            from src.integration.fast_quote_router_v1 import FastQuoteRouterV1  # pylint: disable=import-outside-toplevel

                            router = getattr(self.server, "fast_quote_router_v1", None)  # type: ignore[attr-defined]
                            if router is None:
                                router = FastQuoteRouterV1(max_cache_pairs=32)
                                self.server.fast_quote_router_v1 = router  # type: ignore[attr-defined]
                            topk_max = int(obj.get("fast_topk_max", 32))
                            q = router.quote_exact_in_2hop_fast_v1(
                                pools_by_id=pools_by_id,
                                asset_in=asset_in,
                                asset_out=asset_out,
                                amount_in=amt,
                                topk_max=topk_max,
                            )
                            if q is None:
                                routing_mode_used = "exact"
                                q = best_route_exact_in_2hop(
                                    pools_by_id=pools_by_id,
                                    asset_in=asset_in,
                                    asset_out=asset_out,
                                    amount_in=amt,
                                )
                        except Exception:
                            routing_mode_used = "exact"
                            q = best_route_exact_in_2hop(
                                pools_by_id=pools_by_id,
                                asset_in=asset_in,
                                asset_out=asset_out,
                                amount_in=amt,
                            )
                    else:
                        q = best_route_exact_in_2hop(
                            pools_by_id=pools_by_id,
                            asset_in=asset_in,
                            asset_out=asset_out,
                            amount_in=amt,
                        )
                else:
                    amt = int(obj.get("amount_out", 0))
                    if routing_mode_req == "fast_v1":
                        try:
                            from src.integration.fast_quote_router_v1 import FastQuoteRouterV1  # pylint: disable=import-outside-toplevel

                            router = getattr(self.server, "fast_quote_router_v1", None)  # type: ignore[attr-defined]
                            if router is None:
                                router = FastQuoteRouterV1(max_cache_pairs=32)
                                self.server.fast_quote_router_v1 = router  # type: ignore[attr-defined]
                            topk_max = int(obj.get("fast_topk_max", 32))
                            q = router.quote_exact_out_2hop_fast_v1(
                                pools_by_id=pools_by_id,
                                asset_in=asset_in,
                                asset_out=asset_out,
                                amount_out=amt,
                                topk_max=topk_max,
                                apply_two_hop_gate=bool(obj.get("apply_two_hop_gate", False)),
                            )
                            if q is None:
                                routing_mode_used = "exact"
                                q = best_route_exact_out_2hop(
                                    pools_by_id=pools_by_id,
                                    asset_in=asset_in,
                                    asset_out=asset_out,
                                    amount_out=amt,
                                    apply_two_hop_gate=bool(obj.get("apply_two_hop_gate", False)),
                                )
                        except Exception:
                            routing_mode_used = "exact"
                            q = best_route_exact_out_2hop(
                                pools_by_id=pools_by_id,
                                asset_in=asset_in,
                                asset_out=asset_out,
                                amount_out=amt,
                                apply_two_hop_gate=bool(obj.get("apply_two_hop_gate", False)),
                            )
                    else:
                        q = best_route_exact_out_2hop(
                            pools_by_id=pools_by_id,
                            asset_in=asset_in,
                            asset_out=asset_out,
                            amount_out=amt,
                            apply_two_hop_gate=bool(obj.get("apply_two_hop_gate", False)),
                        )
                if q is None:
                    self._write_json(200, {"ok": False, "error": "no_route"}, cors_origin=cors_origin)
                    return True
                receipt = make_route_quote_receipt(kind=kind, quote=q, pools_by_id=pools_by_id)
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "kind": kind,
                        "routing_mode": str(routing_mode_used),
                        "quote": _quote_to_dict(q),
                        "receipt": receipt,
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                err = "bad_pools" if "pools" in str(exc).lower() else "quote_error"
                self._write_json(400, {"ok": False, "error": err, "details": str(exc)[:200]}, cors_origin=cors_origin)
                return True

        if path == "/api/dex/verify_quote_receipt":
            rec = obj.get("receipt")
            if not isinstance(rec, dict):
                self._write_json(400, {"ok": False, "error": "bad_receipt"}, cors_origin=cors_origin)
                return True
            try:
                pools_by_id = _parse_pools()
                from src.core.quote_receipts import verify_route_quote_receipt  # pylint: disable=import-outside-toplevel

                ok, err = verify_route_quote_receipt(rec, pools_by_id=pools_by_id)
                self._write_json(200, {"ok": bool(ok), "error": str(err)}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(400, {"ok": False, "error": "verify_error", "details": str(exc)[:200]}, cors_origin=cors_origin)
                return True

        self._write_json(404, {"ok": False, "error": "not_found"}, cors_origin=cors_origin)
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
        if self._maybe_handle_dex_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
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
    dex_enabled = _env_str("DEX_API_ENABLED", "false").lower() in ("1", "true", "yes")
    demo_api_token = _env_str("DEMO_API_TOKEN", "")
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env  # pylint: disable=import-outside-toplevel
    confidential_feature_status = load_confidential_feature_status_from_env().to_public_dict()

    if (perps_enabled or zusd_enabled or dex_enabled) and (not demo_api_token) and (not _is_loopback_host(host)):
        print(
            "Refusing to start: demo APIs enabled on non-loopback host without DEMO_API_TOKEN "
            f"(host={host!r}, perps_api={perps_enabled}, zusd_api={zusd_enabled}, dex_api={dex_enabled})"
        )
        return 2

    httpd = ThreadingHTTPServer((host, port), _Handler)
    # Attach config to server instance (used by handler).
    httpd.cors_origins = cors_origins  # type: ignore[attr-defined]
    httpd.rate_limiter = TokenBucketRateLimiter(rpm=rpm, max_buckets=max_buckets)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = perps_enabled  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = zusd_enabled  # type: ignore[attr-defined]
    httpd.dex_api_enabled = dex_enabled  # type: ignore[attr-defined]
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
