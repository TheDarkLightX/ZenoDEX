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
- Bearer-token auth for explicitly approved API routes
  (ZENODEX_API_BEARER_TOKEN, with DEMO_API_TOKEN as a legacy local alias)
"""

from __future__ import annotations

import json
import hmac
import hashlib
import os
import threading
import time
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from math import comb
from typing import Any, Mapping, Optional, Sequence, Set
from urllib.parse import urlsplit

# Prewarm the expensive attestation / LP-aware settlement modules at server
# startup so their first request does not pay import latency inside the 2s API
# timeout budget used by the focused regression suite.
for _prewarm_module_name in (
    "src.integration.operations",
    "src.integration.settlement_price_provenance",
    "src.integration.settlement_price_attestation",
    "src.integration.settlement_end_to_end_certificate_packet",
    "src.integration.settlement_witness_lifecycle",
    "src.integration.settlement_feature_extension_packet",
    "src.integration.settlement_value_contract",
    "src.integration.settlement_lp_value_contract",
    "src.integration.settlement_endogenous_lp_value_packet",
    "src.integration.settlement_value_packet",
):  # pragma: no cover - import latency hygiene only
    try:
        __import__(_prewarm_module_name)
    except Exception:
        pass


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        value = int(default)
    else:
        try:
            value = int(raw.strip())
        except ValueError as exc:
            raise ValueError(
                f"{name} must be an integer in [{lo}, {hi}]; got {raw!r}"
            ) from exc
    if value < lo or value > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}]; got {value}")
    return int(value)


def _env_str(name: str, default: str) -> str:
    raw = os.environ.get(name)
    if raw is None:
        return default
    v = raw.strip()
    return v if v else default


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    value = raw.strip().lower()
    if value in ("1", "true", "yes", "on"):
        return True
    if value in ("0", "false", "no", "off"):
        return False
    raise ValueError(
        f"{name} must be one of 1,true,yes,on,0,false,no,off; got {raw!r}"
    )


def _safe_http_header_value(value: object) -> Optional[str]:
    if not isinstance(value, str):
        return None
    if any(ord(ch) < 0x20 or ord(ch) == 0x7F for ch in value):
        return None
    try:
        value.encode("latin-1")
    except UnicodeEncodeError:
        return None
    return value


def _safe_cors_origin(value: object) -> Optional[str]:
    raw = _safe_http_header_value(value)
    if raw is None:
        return None
    origin = raw.strip()
    if not origin:
        return None
    parsed = urlsplit(origin)
    if parsed.scheme not in ("http", "https"):
        return None
    if not parsed.netloc or parsed.username or parsed.password:
        return None
    if parsed.query or parsed.fragment:
        return None
    if parsed.path not in ("", "/"):
        return None
    return f"{parsed.scheme}://{parsed.netloc}"


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
        origin = _safe_cors_origin(item)
        if origin is None:
            continue
        if origin == "*":
            # Explicitly refuse wildcard; force operators to list trusted origins.
            continue
        out.add(origin)
    return out


from src.integration.api_server_settlement_parsers import (
    _parse_price_history_payload,
    _parse_settlement_feature_extension_inputs_payload,
    _parse_settlement_proof_flags_payload,
)
from src.state.canonical import canonical_json_bytes


DEX_API_MAX_ROUTE_AMOUNT_IN = 50_000
DEX_API_MAX_TWO_POOL_AUDIT_AMOUNT_OUT_TOTAL = 512
DEX_API_MAX_SANDWICH_ATTACKER_AMOUNT_IN = 50_000
DEX_API_MAX_SLIPPAGE_OPTIONS = 64
DEX_API_MAX_POOLS = 64
DEX_API_MAX_MIXED_DIRECT_TWOHOP_SPLIT_AMOUNT_IN = 5_000
DEX_API_MAX_FAST_TOPK = 4_096
DEX_API_EXACT_OUT_CANDIDATE_EVAL_BUDGET = 4_096
DEX_API_EXACT_OUT_SEARCH_CAPS = {
    "amount_out_total": (1, DEX_API_MAX_ROUTE_AMOUNT_IN),
    "max_legs": (1, 3),
    "max_candidate_pools": (1, 5),
    "max_candidates": (1, 12),
    "max_iters": (1, 4_096),
    "window": (0, 64),
    "brute_force_max": (0, 512),
    "max_full_domain_pools": (1, 16),
    "max_enumerated_candidates": (1, 50_000),
}
DEX_API_EXACT_IN_ROUTE_SEARCH_PATHS = {
    "/api/dex/build_exact_in_route_oracle_contract",
    "/api/dex/guard_exact_in_route_canonicality",
    "/api/dex/quote_exact_in_route_guarded",
    "/api/dex/build_exact_in_route_guarded_quote_packet",
    "/api/dex/build_exact_in_route_rank_projection_packet",
    "/api/dex/build_exact_in_route_true_key_interpretation_packet",
}
DEX_ROUTING_REFERENCE_QUERY_ID = (
    "sha256:"
    + hashlib.sha256("zenodex.oracle.query.routing.reference_price_e8".encode("utf-8")).hexdigest()
)
_ORACLE_CONSUMER_PROFILE_SCHEMA = "zenodex.oracle.consumer_profile.v1"
DEX_ROUTING_GUARDED_QUOTE_PROFILE_ID = "sha256:" + hashlib.sha256(
    canonical_json_bytes(
        {
            "schema": _ORACLE_CONSUMER_PROFILE_SCHEMA,
            "consumer_module": "zenodex.routing",
            "action_kind": "guarded_quote",
            "query_id": DEX_ROUTING_REFERENCE_QUERY_ID,
            "required_evidence_floor": "O3",
            "max_freshness_window_epochs": 4,
            "critical": True,
        }
    )
).hexdigest()


def _is_loopback_host(host: str) -> bool:
    h = (host or "").strip().lower()
    return h in ("127.0.0.1", "localhost", "::1")


def _dex_api_int_limit_error(
    obj: dict[str, Any],
    *,
    field: str,
    min_value: int,
    max_value: int,
) -> Optional[str]:
    if field not in obj:
        return None
    value = obj.get(field)
    if not isinstance(value, int) or isinstance(value, bool):
        return f"bad_{field}"
    if int(value) < int(min_value) or int(value) > int(max_value):
        return f"bad_{field}"
    return None


def _dex_api_list_length_error(
    obj: dict[str, Any],
    *,
    field: str,
    max_len: int,
) -> Optional[str]:
    if field not in obj:
        return None
    value = obj.get(field)
    if isinstance(value, list) and len(value) > int(max_len):
        return f"bad_{field}"
    return None


def _dex_api_nested_int_limit_error(
    value: Any,
    *,
    field: str,
    min_value: int,
    max_value: int,
    max_depth: int = 32,
) -> Optional[str]:
    if max_depth < 0:
        return "bad_request_depth"
    if isinstance(value, dict):
        if field in value:
            raw = value.get(field)
            if not isinstance(raw, int) or isinstance(raw, bool):
                return f"bad_{field}"
            if int(raw) < int(min_value) or int(raw) > int(max_value):
                return f"bad_{field}"
        for child in value.values():
            err = _dex_api_nested_int_limit_error(
                child,
                field=field,
                min_value=min_value,
                max_value=max_value,
                max_depth=max_depth - 1,
            )
            if err is not None:
                return err
    elif isinstance(value, list):
        for child in value:
            err = _dex_api_nested_int_limit_error(
                child,
                field=field,
                min_value=min_value,
                max_value=max_value,
                max_depth=max_depth - 1,
            )
            if err is not None:
                return err
    return None


def _dex_api_nested_list_length_error(
    value: Any,
    *,
    field: str,
    max_len: int,
    max_depth: int = 32,
) -> Optional[str]:
    if max_depth < 0:
        return "bad_request_depth"
    if isinstance(value, dict):
        raw = value.get(field)
        if isinstance(raw, list) and len(raw) > int(max_len):
            return f"bad_{field}"
        for child in value.values():
            err = _dex_api_nested_list_length_error(
                child,
                field=field,
                max_len=max_len,
                max_depth=max_depth - 1,
            )
            if err is not None:
                return err
    elif isinstance(value, list):
        for child in value:
            err = _dex_api_nested_list_length_error(
                child,
                field=field,
                max_len=max_len,
                max_depth=max_depth - 1,
            )
            if err is not None:
                return err
    return None


def _dex_api_mixed_exact_in_split_limit_error(params: dict[str, Any]) -> Optional[str]:
    if params.get("enable_mixed_direct_twohop_split") is not True:
        return None
    amount_in = params.get("amount_in")
    if not isinstance(amount_in, int) or isinstance(amount_in, bool):
        return "bad_amount_in"
    if int(amount_in) > DEX_API_MAX_MIXED_DIRECT_TWOHOP_SPLIT_AMOUNT_IN:
        return "bad_amount_in"
    return None


def _dex_api_nested_mixed_exact_in_split_limit_error(value: Any, *, max_depth: int = 32) -> Optional[str]:
    if max_depth < 0:
        return "bad_request_depth"
    if isinstance(value, dict):
        err = _dex_api_mixed_exact_in_split_limit_error(value)
        if err is not None:
            return err
        for child in value.values():
            err = _dex_api_nested_mixed_exact_in_split_limit_error(child, max_depth=max_depth - 1)
            if err is not None:
                return err
    elif isinstance(value, list):
        for child in value:
            err = _dex_api_nested_mixed_exact_in_split_limit_error(child, max_depth=max_depth - 1)
            if err is not None:
                return err
    return None


def _dex_api_exact_out_candidate_space_upper_bound(
    *,
    amount_out_total: int,
    max_candidate_pools: int,
    max_legs: int,
    stop_after: int,
) -> int:
    total = 0
    amount = int(amount_out_total)
    pools = int(max_candidate_pools)
    legs = min(int(max_legs), pools, amount)
    if amount <= 0 or pools <= 0 or legs <= 0:
        return 0
    for k in range(1, legs + 1):
        total += int(comb(pools, k)) * int(comb(amount - 1, k - 1))
        if total > int(stop_after):
            return int(total)
    return int(total)


def _dex_api_exact_out_search_budget_error(params: dict[str, Any]) -> Optional[str]:
    amount_out_total = params.get("amount_out_total")
    if not isinstance(amount_out_total, int) or isinstance(amount_out_total, bool):
        return None
    max_candidate_pools = params.get("max_candidate_pools", 5)
    max_legs = params.get("max_legs", 3)
    max_enumerated_candidates = params.get("max_enumerated_candidates", 20_000)
    for raw in (max_candidate_pools, max_legs, max_enumerated_candidates):
        if not isinstance(raw, int) or isinstance(raw, bool):
            return None
    candidate_space = _dex_api_exact_out_candidate_space_upper_bound(
        amount_out_total=int(amount_out_total),
        max_candidate_pools=int(max_candidate_pools),
        max_legs=int(max_legs),
        stop_after=max(
            DEX_API_EXACT_OUT_CANDIDATE_EVAL_BUDGET,
            int(max_enumerated_candidates),
        ),
    )
    if candidate_space > int(max_enumerated_candidates):
        return "bad_exact_out_search_budget"
    effective_budget = min(int(max_enumerated_candidates), int(candidate_space))
    if effective_budget > DEX_API_EXACT_OUT_CANDIDATE_EVAL_BUDGET:
        return "bad_exact_out_search_budget"
    return None


def _dex_api_nested_exact_out_search_budget_error(value: Any, *, max_depth: int = 32) -> Optional[str]:
    if max_depth < 0:
        return "bad_request_depth"
    if isinstance(value, dict):
        has_search_shape = "amount_out_total" in value and (
            "max_enumerated_candidates" in value or "max_candidate_pools" in value or "max_legs" in value
        )
        if has_search_shape:
            err = _dex_api_exact_out_search_budget_error(value)
            if err is not None:
                return err
        for child in value.values():
            err = _dex_api_nested_exact_out_search_budget_error(child, max_depth=max_depth - 1)
            if err is not None:
                return err
    elif isinstance(value, list):
        for child in value:
            err = _dex_api_nested_exact_out_search_budget_error(child, max_depth=max_depth - 1)
            if err is not None:
                return err
    return None


def _is_exact_out_many_pool_search_path(path: str) -> bool:
    return (
        path.startswith("/api/dex/quote_exact_out_many_pool")
        or path.startswith("/api/dex/build_exact_out_many_pool")
        or path in {
            "/api/dex/audit_exact_out_many_pool_canonicality",
            "/api/dex/guard_exact_out_many_pool_canonicality",
        }
    )


def _is_exact_out_many_pool_verify_path(path: str) -> bool:
    return path.startswith("/api/dex/verify_exact_out_many_pool_")


def _is_exact_in_route_verify_path(path: str) -> bool:
    return path.startswith("/api/dex/verify_exact_in_route_")


def _dex_api_search_limit_error(path: str, obj: dict[str, Any]) -> Optional[str]:
    err = _dex_api_list_length_error(
        obj,
        field="pools",
        max_len=DEX_API_MAX_POOLS,
    )
    if err is not None:
        return err

    if path in {"/api/dex/impact_preview", "/api/dex/slippage_advice"}:
        err = _dex_api_int_limit_error(
            obj,
            field="amount_in",
            min_value=0,
            max_value=DEX_API_MAX_ROUTE_AMOUNT_IN,
        )
        if err is not None:
            return err

    if path in {
        "/api/dex/slippage_advice",
        "/api/dex/pokayoke_swap_suggest",
        "/api/dex/pokayoke_swap_suggest_heavy",
    }:
        err = _dex_api_int_limit_error(
            obj,
            field="max_attacker_amount_in",
            min_value=0,
            max_value=DEX_API_MAX_SANDWICH_ATTACKER_AMOUNT_IN,
        )
        if err is not None:
            return err
        err = _dex_api_list_length_error(
            obj,
            field="slippage_options_bps",
            max_len=DEX_API_MAX_SLIPPAGE_OPTIONS,
        )
        if err is not None:
            return err
        if path in {"/api/dex/pokayoke_swap_suggest", "/api/dex/pokayoke_swap_suggest_heavy"}:
            err = _dex_api_int_limit_error(
                obj,
                field="amount_in",
                min_value=1,
                max_value=DEX_API_MAX_ROUTE_AMOUNT_IN,
            )
            if err is not None:
                return err

    if path == "/api/dex/quote":
        kind = str(obj.get("kind", "")).strip().lower()
        if kind == "exact_in":
            err = _dex_api_int_limit_error(
                obj,
                field="amount_in",
                min_value=1,
                max_value=DEX_API_MAX_ROUTE_AMOUNT_IN,
            )
            if err is not None:
                return err
        elif kind == "exact_out":
            err = _dex_api_int_limit_error(
                obj,
                field="amount_out",
                min_value=1,
                max_value=DEX_API_MAX_ROUTE_AMOUNT_IN,
            )
            if err is not None:
                return err
        if str(obj.get("routing_mode", "exact")).strip().lower() == "fast_v1":
            err = _dex_api_int_limit_error(
                obj,
                field="fast_topk_max",
                min_value=1,
                max_value=DEX_API_MAX_FAST_TOPK,
            )
            if err is not None:
                return err

    if path in DEX_API_EXACT_IN_ROUTE_SEARCH_PATHS:
        err = _dex_api_int_limit_error(
            obj,
            field="amount_in",
            min_value=1,
            max_value=DEX_API_MAX_ROUTE_AMOUNT_IN,
        )
        if err is not None:
            return err
        err = _dex_api_mixed_exact_in_split_limit_error(obj)
        if err is not None:
            return err

    if path == "/api/dex/audit_exact_out_two_pool_canonicality":
        err = _dex_api_int_limit_error(
            obj,
            field="amount_out_total",
            min_value=1,
            max_value=DEX_API_MAX_TWO_POOL_AUDIT_AMOUNT_OUT_TOTAL,
        )
        if err is not None:
            return err
        err = _dex_api_int_limit_error(
            obj,
            field="brute_force_max",
            min_value=0,
            max_value=DEX_API_MAX_TWO_POOL_AUDIT_AMOUNT_OUT_TOTAL,
        )
        if err is not None:
            return err

    if _is_exact_in_route_verify_path(path):
        err = _dex_api_nested_list_length_error(
            obj,
            field="pool_snapshots",
            max_len=DEX_API_MAX_POOLS,
        )
        if err is not None:
            return err
        err = _dex_api_nested_int_limit_error(
            obj,
            field="amount_in",
            min_value=1,
            max_value=DEX_API_MAX_ROUTE_AMOUNT_IN,
        )
        if err is not None:
            return err
        err = _dex_api_nested_mixed_exact_in_split_limit_error(obj)
        if err is not None:
            return err

    if _is_exact_out_many_pool_verify_path(path):
        err = _dex_api_nested_list_length_error(
            obj,
            field="pool_snapshots",
            max_len=DEX_API_MAX_POOLS,
        )
        if err is not None:
            return err
        for field, (min_value, max_value) in DEX_API_EXACT_OUT_SEARCH_CAPS.items():
            err = _dex_api_nested_int_limit_error(
                obj,
                field=field,
                min_value=int(min_value),
                max_value=int(max_value),
            )
            if err is not None:
                return err
        err = _dex_api_nested_exact_out_search_budget_error(obj)
        if err is not None:
            return err

    if _is_exact_out_many_pool_search_path(path):
        for field, (min_value, max_value) in DEX_API_EXACT_OUT_SEARCH_CAPS.items():
            err = _dex_api_int_limit_error(
                obj,
                field=field,
                min_value=int(min_value),
                max_value=int(max_value),
            )
            if err is not None:
                return err
        err = _dex_api_exact_out_search_budget_error(obj)
        if err is not None:
            return err

    return None


def _adapter_result_get(result: Any, key: str) -> Any:
    if isinstance(result, Mapping):
        return result.get(key)
    return getattr(result, key, None)


def _adapter_error_summary(result: Any) -> str:
    errors = _adapter_result_get(result, "errors")
    if isinstance(errors, (list, tuple)):
        parts = [str(x) for x in errors[:3]]
        if parts:
            return "; ".join(parts)
    return "bridge verifier rejected"


def _canonical_routing_pool_snapshots(pools_raw: object) -> list[dict[str, Any]]:
    if not isinstance(pools_raw, list):
        raise ValueError("pools_must_be_list")
    snapshots: list[dict[str, Any]] = []
    for row in pools_raw:
        if not isinstance(row, Mapping):
            raise ValueError("pool_must_be_object")
        snapshots.append(
            {
                "pool_id": str(row.get("pool_id", "")),
                "asset0": str(row.get("asset0", "")),
                "asset1": str(row.get("asset1", "")),
                "reserve0": int(row.get("reserve0", 0)),
                "reserve1": int(row.get("reserve1", 0)),
                "fee_bps": int(row.get("fee_bps", 0)),
                "lp_supply": int(row.get("lp_supply", 1)),
                "status": str(row.get("status", "ACTIVE")).strip().upper(),
                "created_at": int(row.get("created_at", 0)),
                "curve_tag": str(row.get("curve_tag", "CPMM")),
                "curve_params": row.get("curve_params", ""),
            }
        )
    return snapshots


def _routing_guarded_quote_oracle_action_id(
    *,
    path: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    split_search_profile: str,
    enable_mixed_direct_twohop_split: bool,
    binding_ok: int,
    pools_raw: object,
) -> str:
    pool_snapshots = _canonical_routing_pool_snapshots(pools_raw)
    pool_snapshot_hash = "sha256:" + hashlib.sha256(canonical_json_bytes({"pools": pool_snapshots})).hexdigest()
    payload = {
        "schema": "zenodex.oracle.routing_runtime_action_id.v1",
        "consumer_module": "zenodex.routing",
        "action_kind": "guarded_quote",
        "path": path,
        "quote_kind": "exact_in",
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": int(amount_in),
        "split_search_profile": split_search_profile,
        "enable_mixed_direct_twohop_split": bool(enable_mixed_direct_twohop_split),
        "binding_ok": int(binding_ok),
        "pool_snapshot_hash": pool_snapshot_hash,
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _routing_guarded_exact_out_quote_oracle_action_id(
    *,
    path: str,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int,
    max_candidate_pools: int,
    max_candidates: int,
    max_iters: int,
    window: int,
    brute_force_max: int,
    max_enumerated_candidates: int,
    pools_raw: object,
) -> str:
    pool_snapshots = _canonical_routing_pool_snapshots(pools_raw)
    pool_snapshot_hash = "sha256:" + hashlib.sha256(canonical_json_bytes({"pools": pool_snapshots})).hexdigest()
    payload = {
        "schema": "zenodex.oracle.routing_runtime_action_id.v1",
        "consumer_module": "zenodex.routing",
        "action_kind": "guarded_quote",
        "path": path,
        "quote_kind": "exact_out_many_pool",
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_out_total": int(amount_out_total),
        "max_legs": int(max_legs),
        "max_candidate_pools": int(max_candidate_pools),
        "max_candidates": int(max_candidates),
        "max_iters": int(max_iters),
        "window": int(window),
        "brute_force_max": int(brute_force_max),
        "max_enumerated_candidates": int(max_enumerated_candidates),
        "pool_snapshot_hash": pool_snapshot_hash,
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _check_routing_oracle_adapter_bridge_for_action(
    *,
    body: Mapping[str, Any],
    expected_action_id: str,
) -> Optional[str]:
    required = _env_bool("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", default=False)
    if "oracle_adapter_bridge" not in body:
        if required:
            return "guarded_quote requires oracle_adapter_bridge"
        return None

    bridge = body.get("oracle_adapter_bridge")
    if not isinstance(bridge, Mapping):
        return "oracle_adapter_bridge must be an object"

    try:
        from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
            verify_aggregate_adapter_bridge,
        )
    except Exception as exc:
        return f"oracle_adapter_bridge verifier unavailable: {type(exc).__name__}"

    try:
        result = verify_aggregate_adapter_bridge(bridge)
    except Exception as exc:
        return f"oracle_adapter_bridge verifier error: {type(exc).__name__}"

    if _adapter_result_get(result, "status") != "accepted":
        return f"oracle_adapter_bridge rejected: {_adapter_error_summary(result)}"
    if _adapter_result_get(result, "consumer_module") != "zenodex.routing":
        return "oracle_adapter_bridge consumer mismatch"
    if _adapter_result_get(result, "action_kind") != "guarded_quote":
        return "oracle_adapter_bridge action mismatch"
    if _adapter_result_get(result, "query_id") != DEX_ROUTING_REFERENCE_QUERY_ID:
        return "oracle_adapter_bridge query mismatch"
    if _adapter_result_get(result, "profile_id") != DEX_ROUTING_GUARDED_QUOTE_PROFILE_ID:
        return "oracle_adapter_bridge profile mismatch"
    if _adapter_result_get(result, "action_id") != expected_action_id:
        return "oracle_adapter_bridge action_id mismatch"
    return None


def _check_routing_oracle_adapter_bridge(
    *,
    body: Mapping[str, Any],
    path: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    split_search_profile: str,
    enable_mixed_direct_twohop_split: bool,
    binding_ok: int,
) -> Optional[str]:
    if "oracle_adapter_bridge" not in body:
        if _env_bool("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", default=False):
            return "guarded_quote requires oracle_adapter_bridge"
        return None
    try:
        expected_action_id = _routing_guarded_quote_oracle_action_id(
            path=path,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=int(amount_in),
            split_search_profile=split_search_profile,
            enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
            binding_ok=int(binding_ok),
            pools_raw=body.get("pools"),
        )
    except (TypeError, ValueError):
        return "oracle_adapter_bridge action_id unavailable"
    return _check_routing_oracle_adapter_bridge_for_action(
        body=body,
        expected_action_id=expected_action_id,
    )


def _check_routing_exact_out_oracle_adapter_bridge(
    *,
    body: Mapping[str, Any],
    path: str,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int,
    max_candidate_pools: int,
    max_candidates: int,
    max_iters: int,
    window: int,
    brute_force_max: int,
    max_enumerated_candidates: int,
) -> Optional[str]:
    if "oracle_adapter_bridge" not in body:
        if _env_bool("DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", default=False):
            return "guarded_quote requires oracle_adapter_bridge"
        return None
    try:
        expected_action_id = _routing_guarded_exact_out_quote_oracle_action_id(
            path=path,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=int(max_candidate_pools),
            max_candidates=int(max_candidates),
            max_iters=int(max_iters),
            window=int(window),
            brute_force_max=int(brute_force_max),
            max_enumerated_candidates=int(max_enumerated_candidates),
            pools_raw=body.get("pools"),
        )
    except (TypeError, ValueError):
        return "oracle_adapter_bridge action_id unavailable"
    return _check_routing_oracle_adapter_bridge_for_action(
        body=body,
        expected_action_id=expected_action_id,
    )


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
        return _safe_cors_origin(origin)

    def _write_json(self, status: int, obj: object, *, cors_origin: Optional[str]) -> None:
        body = json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        safe_cors_origin = _safe_cors_origin(cors_origin) if cors_origin is not None else None
        self.send_response(int(status))
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        if int(status) == 401:
            # Hint for clients and intermediaries (even though we don't use Basic auth).
            self.send_header("WWW-Authenticate", "Bearer")
        self.send_header("Content-Length", str(len(body)))
        if safe_cors_origin is not None and "\r" not in safe_cors_origin and "\n" not in safe_cors_origin:
            self.send_header("Access-Control-Allow-Origin", safe_cors_origin)
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
        for allowed_origin in allowed:
            if origin == allowed_origin:
                return allowed_origin
        return None

    def _demo_auth_ok(self) -> bool:
        """Optional bearer token auth for demo/dev routes.

        If no token is configured, auth is not enforced by the handler. main()
        refuses that configuration for enabled sensitive APIs unless an external
        auth boundary is explicitly declared.
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

    def _max_post_body_bytes_for_path(self, path: str) -> int:
        """Return the bounded request-body limit for a POST path."""
        if path.startswith("/api/dex/verify_exact_out_many_pool_"):
            # Witness-preserving exact-out certificate packets can exceed 64 KiB once
            # they include full bounded-domain candidate streams and domination witnesses.
            return 262_144
        if path.startswith("/api/strategy/autotrader/"):
            return 96_000
        if path.startswith("/api/confidential/attestation/"):
            return 96_000
        if path.startswith("/api/confidential/sealed-bid/"):
            return 96_000
        if path.startswith("/api/autogov/"):
            return 8 * 1024 * 1024
        return 65_536

    def _perps_state(self) -> Any:
        """Get the current PerpsState from the server (may be None)."""
        return getattr(self.server, "perps_state", None)

    def _maybe_handle_perps_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/perps/"):
            return False
        if path.startswith("/api/perps/wallet/"):
            return self._maybe_handle_perps_wallet_api(
                method=method,
                path=path,
                cors_origin=cors_origin,
                raw_body=raw_body,
            )
        if not getattr(self.server, "perps_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.perps_api import handle_perps_request

        status, resp = handle_perps_request(method, path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_perps_wallet_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/perps/wallet/"):
            return False
        if not getattr(self.server, "perps_wallet_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.perps_wallet_api import handle_perps_wallet_request

        # Pass the query-bearing raw path so the handler can resolve ?account=.
        status, resp = handle_perps_wallet_request(method, self.path or path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_autogov_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/autogov/"):
            return False
        if not getattr(self.server, "autogov_live_apply_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.autogov_live_apply_api import handle_autogov_request

        status, resp = handle_autogov_request(method, path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_zusd_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/zusd/"):
            return False
        if path.startswith("/api/zusd/monetary/"):
            return self._maybe_handle_zusd_monetary_wallet_api(
                method=method,
                path=path,
                cors_origin=cors_origin,
                raw_body=raw_body,
            )
        if path.startswith("/api/zusd/wallet/"):
            return self._maybe_handle_zusd_tau_wallet_api(
                method=method,
                path=path,
                cors_origin=cors_origin,
                raw_body=raw_body,
            )
        if not getattr(self.server, "zusd_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.zusd_api import handle_zusd_request

        status, resp = handle_zusd_request(method, path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_zusd_tau_wallet_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/zusd/wallet/"):
            return False
        if not getattr(self.server, "zusd_tau_wallet_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.zusd_tau_wallet_api import handle_zusd_tau_wallet_request

        # Pass the query-bearing raw path so the handler can resolve ?account=.
        status, resp = handle_zusd_tau_wallet_request(method, self.path or path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_zusd_monetary_wallet_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/zusd/monetary/"):
            return False
        if not getattr(self.server, "zusd_monetary_wallet_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.zusd_monetary_wallet_api import handle_zusd_monetary_wallet_request

        # Pass the query-bearing raw path so the handler can resolve ?account=.
        status, resp = handle_zusd_monetary_wallet_request(method, self.path or path, raw_body)
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_autotrader_live_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/strategy/autotrader/"):
            return False
        if not getattr(self.server, "autotrader_live_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.autotrader_live_api import handle_autotrader_live_request

        execution_keys = getattr(self.server, "autotrader_execution_keys", None)  # type: ignore[attr-defined]
        supervisor_runs = getattr(self.server, "autotrader_supervisor_runs", None)  # type: ignore[attr-defined]
        execution_lock = getattr(self.server, "autotrader_execution_lock", None)  # type: ignore[attr-defined]
        if path in {
            "/api/strategy/autotrader/execute-once",
            "/api/strategy/autotrader/supervisor/execute",
        } and execution_lock is not None:
            with execution_lock:
                status, resp = handle_autotrader_live_request(
                    method,
                    path,
                    raw_body,
                    execution_keys=execution_keys,
                    supervisor_runs=supervisor_runs,
                )
        else:
            status, resp = handle_autotrader_live_request(
                method,
                path,
                raw_body,
                execution_keys=execution_keys,
                supervisor_runs=supervisor_runs,
            )
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_confidential_attestation_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/confidential/attestation/"):
            return False
        if not getattr(self.server, "confidential_attestation_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.confidential_attestation_api import handle_confidential_attestation_request

        request_table = getattr(self.server, "confidential_request_table", None)  # type: ignore[attr-defined]
        request_lock = getattr(self.server, "confidential_request_lock", None)  # type: ignore[attr-defined]
        if path in {
            "/api/confidential/attestation/admit",
            "/api/confidential/attestation/execute",
        } and request_lock is not None:
            with request_lock:
                status, resp = handle_confidential_attestation_request(
                    method,
                    path,
                    raw_body,
                    request_table=request_table,
                )
        else:
            status, resp = handle_confidential_attestation_request(
                method,
                path,
                raw_body,
                request_table=request_table,
            )
        self._write_json(status, resp, cors_origin=cors_origin)
        return True

    def _maybe_handle_confidential_sealed_bid_api(
        self, *, method: str, path: str, cors_origin: Optional[str], raw_body: Optional[bytes]
    ) -> bool:
        if not path.startswith("/api/confidential/sealed-bid/"):
            return False
        if not getattr(self.server, "confidential_sealed_bid_api_enabled", False):
            return False
        if not self._demo_auth_ok():
            self._write_json(401, {"ok": False, "error": "unauthorized"}, cors_origin=cors_origin)
            return True
        from src.integration.confidential_sealed_bid_api import handle_confidential_sealed_bid_request

        state_store = getattr(self.server, "confidential_sealed_bid_state", None)  # type: ignore[attr-defined]
        if not isinstance(state_store, dict):
            state_store = {}
            setattr(self.server, "confidential_sealed_bid_state", state_store)
        state_file = getattr(self.server, "confidential_sealed_bid_state_file", "")  # type: ignore[attr-defined]
        if not isinstance(state_file, str):
            state_file = ""
        state_lock = getattr(self.server, "confidential_sealed_bid_lock", None)  # type: ignore[attr-defined]
        if state_lock is not None:
            with state_lock:
                status, resp = handle_confidential_sealed_bid_request(
                    method,
                    path,
                    raw_body,
                    state_store=state_store,
                    state_file=state_file,
                )
        else:
            status, resp = handle_confidential_sealed_bid_request(
                method,
                path,
                raw_body,
                state_store=state_store,
                state_file=state_file,
            )
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
        search_limit_error = _dex_api_search_limit_error(path, obj)
        if search_limit_error is not None:
            self._write_json(400, {"ok": False, "error": search_limit_error}, cors_origin=cors_origin)
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
                    {"ok": False, "error": "impact_preview_error", "details": "request failed"},
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
                    {"ok": False, "error": "slippage_advice_error", "details": "request failed"},
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
                    {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"},
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
                    {"ok": False, "error": "pokayoke_swap_suggest_heavy_error", "details": "request failed"},
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
            if "proof_mining_context" in obj:
                self._write_json(400, {"ok": False, "error": "proof_mining_context_not_accepted"}, cors_origin=cors_origin)
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
                    proof_mining_context_obj=None,
                )
                self._write_json(200, {"ok": True, "status": status.to_public_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "proof_mining_status_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/proof_mining_payout_template":
            # Build a deterministic proof-mining payout TEMPLATE: a real,
            # well-formed claim (constructed with the canonical core builder)
            # plus the runtime app-state, chain balances, proof context, and the
            # submit transaction the operator would sign and send. The template's
            # proposal binding is derived deterministically from the request
            # inputs (it is a preview, NOT an attestation of a settled on-chain
            # DEX batch). /api/dex/proof_mining_status is a PREFLIGHT: it checks
            # claim internal consistency + budget + flags + context match, but
            # deliberately passes proof_mining_context_obj=None, so it reports
            # claimable=false ("requires verified DEX proof context") for this
            # template — the consistency checks all pass; full claimability is
            # established only when the verified proof context is supplied at
            # actual submission (see the direct-evaluator check in the test).
            try:
                from src.core.proof_mining_claims import (  # pylint: disable=import-outside-toplevel
                    build_proof_mining_claim,
                    schedule_reward_amount,
                )
                from src.integration.proof_mining_context import (  # pylint: disable=import-outside-toplevel
                    ProofMiningContext,
                    proof_mining_context_to_obj,
                )
                from src.integration.proof_mining_runtime import (  # pylint: disable=import-outside-toplevel
                    initialize_proof_mining_runtime_state,
                    proof_mining_runtime_state_to_obj,
                )
                from src.state.canonical import (  # pylint: disable=import-outside-toplevel
                    domain_sep_bytes,
                    sha256_hex,
                )

                def _short_detail(exc: Exception) -> str:
                    detail = " ".join(str(exc).split())
                    return detail[:200]

                chain_id = str(obj.get("chain_id", "")).strip()
                tx_sender_pubkey = str(obj.get("tx_sender_pubkey", "")).strip()
                reward_pool_pubkey = str(obj.get("reward_pool_pubkey", "")).strip()
                if not chain_id:
                    self._write_json(400, {"ok": False, "error": "missing_chain_id"}, cors_origin=cors_origin)
                    return True
                if not tx_sender_pubkey:
                    self._write_json(400, {"ok": False, "error": "missing_tx_sender_pubkey"}, cors_origin=cors_origin)
                    return True
                if not reward_pool_pubkey:
                    self._write_json(400, {"ok": False, "error": "missing_reward_pool_pubkey"}, cors_origin=cors_origin)
                    return True

                # Canonicalize both pubkeys to the SAME 48-byte form the live
                # claimability gate requires, so a template can never be returned
                # for a sender/pool that /api/dex/proof_mining_status would
                # reject as malformed. Use the canonical forms throughout.
                from src.state.canonical import (  # pylint: disable=import-outside-toplevel
                    canonical_hex_fixed_allow_0x,
                )

                try:
                    tx_sender_pubkey = canonical_hex_fixed_allow_0x(
                        tx_sender_pubkey, nbytes=48, name="tx_sender_pubkey"
                    )
                except Exception:
                    self._write_json(400, {"ok": False, "error": "bad_tx_sender_pubkey"}, cors_origin=cors_origin)
                    return True
                try:
                    reward_pool_pubkey = canonical_hex_fixed_allow_0x(
                        reward_pool_pubkey, nbytes=48, name="reward_pool_pubkey"
                    )
                except Exception:
                    self._write_json(400, {"ok": False, "error": "bad_reward_pool_pubkey"}, cors_origin=cors_origin)
                    return True
                # The reward pool and the recipient must be distinct accounts: a
                # shared pubkey would collapse the two chain_balances entries (the
                # recipient's 0 would clobber the pool balance) and the claim
                # would pay the pool to itself.
                if reward_pool_pubkey == tx_sender_pubkey:
                    self._write_json(
                        400,
                        {"ok": False, "error": "reward_pool_pubkey_must_differ_from_sender"},
                        cors_origin=cors_origin,
                    )
                    return True

                def _bounded_nonneg_int(value: Any, *, name: str, default: int) -> int:
                    if value is None:
                        return int(default)
                    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                        raise ValueError(name)
                    return int(value)

                try:
                    base_reward = _bounded_nonneg_int(obj.get("base_reward"), name="base_reward", default=8)
                    epoch = _bounded_nonneg_int(obj.get("epoch"), name="epoch", default=1)
                    proposal_slot = _bounded_nonneg_int(obj.get("proposal_slot"), name="proposal_slot", default=0)
                    prover_id = _bounded_nonneg_int(obj.get("prover_id"), name="prover_id", default=1)
                except ValueError as exc:
                    field = "".join(ch for ch in str(exc) if ch.isalnum() or ch == "_")[:40] or "field"
                    self._write_json(
                        400, {"ok": False, "error": f"bad_{field}"}, cors_origin=cors_origin
                    )
                    return True
                if base_reward <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_base_reward"}, cors_origin=cors_origin)
                    return True

                try:
                    reward_amount = schedule_reward_amount(base_reward=base_reward, epoch=epoch)
                except Exception:
                    self._write_json(400, {"ok": False, "error": "bad_reward_schedule"}, cors_origin=cors_origin)
                    return True

                # Reward pool starting balance: caller-provided (the UI already
                # resolved it from tokenomics) or a safe default that covers the
                # reward. Must be >= reward_amount or the claim fails the budget
                # gate by construction.
                try:
                    reward_pool_before = _bounded_nonneg_int(
                        obj.get("reward_pool_before"),
                        name="reward_pool_before",
                        default=max(int(reward_amount) * 4, int(reward_amount)),
                    )
                except ValueError:
                    self._write_json(400, {"ok": False, "error": "bad_reward_pool_before"}, cors_origin=cors_origin)
                    return True
                if reward_pool_before < reward_amount:
                    self._write_json(
                        400,
                        {"ok": False, "error": "reward_pool_before_below_reward_amount"},
                        cors_origin=cors_origin,
                    )
                    return True

                # Deterministic, request-bound proposal binding (preview, not a
                # settled-state attestation). All four fields hash the same
                # canonical request projection so the template is reproducible
                # and bound to its inputs.
                binding_projection = {
                    "chain_id": chain_id,
                    "tx_sender_pubkey": tx_sender_pubkey,
                    "reward_pool_pubkey": reward_pool_pubkey,
                    "base_reward": int(base_reward),
                    "epoch": int(epoch),
                    "proposal_slot": int(proposal_slot),
                    "prover_id": int(prover_id),
                    "faucet_mint": obj.get("faucet_mint"),
                    "signed_intent": obj.get("signed_intent"),
                }

                def _template_hash(tag: str) -> str:
                    return sha256_hex(
                        domain_sep_bytes(f"zenodex.proof_mining_payout_template/{tag}", version=1)
                        + canonical_json_bytes(binding_projection)
                    )

                witness_sha256 = _template_hash("witness")
                prev_state_hash = _template_hash("prev_state")
                batch_hash = _template_hash("batch")
                dex_hash_after = _template_hash("dex_after")
                round_id = _template_hash("round")[:32]

                try:
                    claim = build_proof_mining_claim(
                        round_obj={
                            "schema": "zenodex/improvement_bounty_round/v1",
                            "ok": True,
                            "job_digest": _template_hash("job")[:32],
                            "winner": {
                                "miner_id": tx_sender_pubkey,
                                "witness_sha256": witness_sha256,
                                "improvement_u64": 1,
                            },
                            "candidates": [],
                            "argmax_certificate": None,
                        },
                        round_id=round_id,
                        reward_pool_before=int(reward_pool_before),
                        base_reward=int(base_reward),
                        epoch=int(epoch),
                        proposal_slot=int(proposal_slot),
                        prover_id=int(prover_id),
                        chain_id=chain_id,
                        prev_state_hash=prev_state_hash,
                        batch_hash=batch_hash,
                        dex_hash_after=dex_hash_after,
                    )
                except Exception as exc:
                    self._write_json(
                        400,
                        {"ok": False, "error": "proof_mining_claim_build_failed", "details": _short_detail(exc)},
                        cors_origin=cors_origin,
                    )
                    return True

                try:
                    runtime_state = initialize_proof_mining_runtime_state(
                        reward_pool_pubkey=reward_pool_pubkey,
                        reward_pool_balance=int(reward_pool_before),
                        claim_artifact=claim,
                    )
                except Exception as exc:
                    self._write_json(
                        400,
                        {"ok": False, "error": "proof_mining_runtime_init_failed", "details": _short_detail(exc)},
                        cors_origin=cors_origin,
                    )
                    return True

                app_state_json = json.dumps(
                    {
                        "schema": "zenodex/tau_app_state/v1",
                        "proof_mining": proof_mining_runtime_state_to_obj(runtime_state),
                    },
                    separators=(",", ":"),
                    sort_keys=True,
                )

                proposal_binding = claim["body"]["proposal_binding"]
                context_obj = proof_mining_context_to_obj(
                    ProofMiningContext(
                        chain_id=str(proposal_binding["chain_id"]),
                        prev_state_hash=str(proposal_binding["prev_state_hash"]),
                        batch_hash=str(proposal_binding["batch_hash"]),
                        witness_hash=str(proposal_binding["witness_hash"]),
                        dex_hash_after=str(proposal_binding["dex_hash_after"]),
                        proposal_hash=str(claim["body"]["proposal_hash"]),
                        proof_scheme="template_preview_v1",
                    )
                )

                # chain_balances are keyed by pubkey: the reward pool holds the
                # pre-payout balance, the recipient starts at 0 (the payout
                # template attests claimability; settlement applies the move).
                chain_balances: dict[str, int] = {
                    reward_pool_pubkey: int(reward_pool_before),
                    tx_sender_pubkey: 0,
                }

                reward_asset_id = str(
                    obj.get("reward_asset_id")
                    or os.environ.get("TAU_DEX_PROOF_MINING_REWARD_ASSET", "")
                ).strip() or None

                status_request = {
                    "claim": claim,
                    "chain_balances": chain_balances,
                    "app_state_json": app_state_json,
                    "tx_sender_pubkey": tx_sender_pubkey,
                    "expected_proposal_hash": str(claim["body"]["proposal_hash"]),
                }

                payout_tx = {
                    "tx_id": "proof-mining-payout-" + _template_hash("tx")[:24],
                    "tx_sender_pubkey": tx_sender_pubkey,
                    "operations": {
                        "24": {
                            "module": "ZenoProofMining",
                            "action": "submit_proof",
                            "claim": claim,
                            "recipient_pubkey": tx_sender_pubkey,
                        }
                    },
                }

                self._write_json(
                    200,
                    {
                        "ok": True,
                        "template_mode": "preview_v1",
                        "status_request": status_request,
                        "proof_mining_context": context_obj,
                        "tx": payout_tx,
                        "reward_pool_pubkey": reward_pool_pubkey,
                        "reward_asset_id": reward_asset_id,
                        "reward_pool_before": int(reward_pool_before),
                        "reward_amount": int(reward_amount),
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "proof_mining_payout_template_error", "details": "request failed"},
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

        def _exact_out_split_quote_from_dict(payload: object):
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

        def _projected_path_from_exact_out_quote_payload(payload: object) -> list[list[object]] | None:
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
                quote_epoch = obj.get("quote_epoch")
                if quote_epoch is not None:
                    if not isinstance(quote_epoch, int) or isinstance(quote_epoch, bool) or quote_epoch < 0:
                        self._write_json(
                            400,
                            {"ok": False, "error": "bad_quote_epoch"},
                            cors_origin=cors_origin,
                        )
                        return True
                receipt = make_route_quote_receipt(
                    kind=kind,
                    quote=q,
                    pools_by_id=pools_by_id,
                    quote_epoch=(None if quote_epoch is None else int(quote_epoch)),
                )
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
                self._write_json(400, {"ok": False, "error": err, "details": "request failed"}, cors_origin=cors_origin)
                return True

        if path == "/api/dex/verify_quote_receipt":
            rec = obj.get("receipt")
            if not isinstance(rec, dict):
                self._write_json(400, {"ok": False, "error": "bad_receipt"}, cors_origin=cors_origin)
                return True
            expected_quote_epoch = obj.get("expected_quote_epoch")
            if expected_quote_epoch is not None:
                if (
                    not isinstance(expected_quote_epoch, int)
                    or isinstance(expected_quote_epoch, bool)
                    or expected_quote_epoch < 0
                ):
                    self._write_json(
                        400,
                        {"ok": False, "error": "bad_expected_quote_epoch"},
                        cors_origin=cors_origin,
                    )
                    return True
            try:
                pools_by_id = _parse_pools()
                from src.core.quote_receipts import verify_route_quote_receipt  # pylint: disable=import-outside-toplevel

                ok, err = verify_route_quote_receipt(
                    rec,
                    pools_by_id=pools_by_id,
                    expected_quote_epoch=(
                        None if expected_quote_epoch is None else int(expected_quote_epoch)
                    ),
                )
                self._write_json(200, {"ok": bool(ok), "error": str(err)}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(400, {"ok": False, "error": "verify_error", "details": "request failed"}, cors_origin=cors_origin)
                return True

        if path == "/api/dex/build_exact_in_route_oracle_contract":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_in = obj.get("amount_in")
                split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
                enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
                binding_ok = obj.get("binding_ok", 1)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_amount_in"}, cors_origin=cors_origin)
                    return True
                if not split_search_profile:
                    self._write_json(400, {"ok": False, "error": "bad_split_search_profile"}, cors_origin=cors_origin)
                    return True
                if not isinstance(enable_mixed_direct_twohop_split, bool):
                    self._write_json(
                        400,
                        {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"},
                        cors_origin=cors_origin,
                    )
                    return True
                if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
                    self._write_json(400, {"ok": False, "error": "bad_binding_ok"}, cors_origin=cors_origin)
                    return True

                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    build_exact_in_route_oracle_contract,
                )

                contract = build_exact_in_route_oracle_contract(
                    pools_by_id=pools_by_id,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    split_search_profile=split_search_profile,
                    enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
                    binding_ok=int(binding_ok),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "contract_schema": "zenodex/exact-in-route-oracle-contract/v1",
                        "verify_contract_endpoint": "/api/dex/verify_exact_in_route_oracle_contract",
                        "contract": contract.to_dict(),
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_exact_in_route_oracle_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_in_route_oracle_contract":
            contract = obj.get("contract")
            if not isinstance(contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_in_route_oracle_contract_payload,
                )

                ok, err = verify_exact_in_route_oracle_contract_payload(contract)
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_exact_in_route_oracle_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/guard_exact_in_route_canonicality":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_in = obj.get("amount_in")
                split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
                enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
                binding_ok = obj.get("binding_ok", 1)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_amount_in"}, cors_origin=cors_origin)
                    return True
                if not split_search_profile:
                    self._write_json(400, {"ok": False, "error": "bad_split_search_profile"}, cors_origin=cors_origin)
                    return True
                if not isinstance(enable_mixed_direct_twohop_split, bool):
                    self._write_json(
                        400,
                        {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"},
                        cors_origin=cors_origin,
                    )
                    return True
                if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
                    self._write_json(400, {"ok": False, "error": "bad_binding_ok"}, cors_origin=cors_origin)
                    return True

                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    guard_exact_in_route_runtime_canonicality,
                )

                ok, err, contract = guard_exact_in_route_runtime_canonicality(
                    pools_by_id=pools_by_id,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    split_search_profile=split_search_profile,
                    enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
                    binding_ok=int(binding_ok),
                )
                response = {"ok": bool(ok), "contract": contract.to_dict(), "error": err}
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "guard_exact_in_route_canonicality_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_in_route_guarded":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_in = obj.get("amount_in")
                split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
                enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
                binding_ok = obj.get("binding_ok", 1)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_amount_in"}, cors_origin=cors_origin)
                    return True
                if not split_search_profile:
                    self._write_json(400, {"ok": False, "error": "bad_split_search_profile"}, cors_origin=cors_origin)
                    return True
                if not isinstance(enable_mixed_direct_twohop_split, bool):
                    self._write_json(
                        400,
                        {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"},
                        cors_origin=cors_origin,
                    )
                    return True
                if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
                    self._write_json(400, {"ok": False, "error": "bad_binding_ok"}, cors_origin=cors_origin)
                    return True
                bridge_err = _check_routing_oracle_adapter_bridge(
                    body=obj,
                    path=path,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    split_search_profile=split_search_profile,
                    enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
                    binding_ok=int(binding_ok),
                )
                if bridge_err is not None:
                    self._write_json(
                        400,
                        {"ok": False, "error": "rejected", "detail": bridge_err},
                        cors_origin=cors_origin,
                    )
                    return True

                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    quote_exact_in_route_guarded,
                )

                quote, err, contract = quote_exact_in_route_guarded(
                    pools_by_id=pools_by_id,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    split_search_profile=split_search_profile,
                    enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
                    binding_ok=int(binding_ok),
                )
                response = {"ok": quote is not None, "contract": contract.to_dict(), "error": err}
                if quote is not None:
                    response["quote"] = contract.to_dict()["runtime_quote"]
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "quote_exact_in_route_guarded_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_in_route_guarded_quote_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_in = obj.get("amount_in")
                split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
                enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
                binding_ok = obj.get("binding_ok", 1)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_amount_in"}, cors_origin=cors_origin)
                    return True
                if not split_search_profile:
                    self._write_json(400, {"ok": False, "error": "bad_split_search_profile"}, cors_origin=cors_origin)
                    return True
                if not isinstance(enable_mixed_direct_twohop_split, bool):
                    self._write_json(
                        400,
                        {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"},
                        cors_origin=cors_origin,
                    )
                    return True
                if not isinstance(binding_ok, int) or isinstance(binding_ok, bool) or binding_ok not in {0, 1}:
                    self._write_json(400, {"ok": False, "error": "bad_binding_ok"}, cors_origin=cors_origin)
                    return True

                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    build_exact_in_route_guarded_quote_packet,
                )

                packet = build_exact_in_route_guarded_quote_packet(
                    pools_by_id=pools_by_id,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    split_search_profile=split_search_profile,
                    enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
                    binding_ok=int(binding_ok),
                )
                packet_dict = packet.to_dict()
                response = {
                    "ok": True,
                    "packet_schema": "zenodex/exact-in-route-guarded-quote-packet/v1",
                    "verify_packet_endpoint": "/api/dex/verify_exact_in_route_guarded_quote_packet",
                    "packet": packet_dict,
                }
                if not packet.guard_ok:
                    response["guard_ok"] = False
                    response["error"] = str(packet.error or "exact_in_runtime_not_canonical")
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_exact_in_route_guarded_quote_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_in_route_guarded_quote_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_in_route_guarded_quote_packet_payload,
                )

                ok, err = verify_exact_in_route_guarded_quote_packet_payload(packet)
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_exact_in_route_guarded_quote_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_in_route_rank_projection_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_in = obj.get("amount_in")
                split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
                enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_amount_in"}, cors_origin=cors_origin)
                    return True
                if not split_search_profile:
                    self._write_json(400, {"ok": False, "error": "bad_split_search_profile"}, cors_origin=cors_origin)
                    return True
                if not isinstance(enable_mixed_direct_twohop_split, bool):
                    self._write_json(
                        400,
                        {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"},
                        cors_origin=cors_origin,
                    )
                    return True

                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    build_exact_in_route_rank_projection_packet_for_pools,
                )

                packet = build_exact_in_route_rank_projection_packet_for_pools(
                    pools_by_id=pools_by_id,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    split_search_profile=split_search_profile,
                    enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
                )
                if packet is None:
                    self._write_json(200, {"ok": False, "error": "no_route_candidates"}, cors_origin=cors_origin)
                    return True
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "packet_schema": "zenodex/exact-in-route-rank-projection-packet/v1",
                        "verify_packet_endpoint": "/api/dex/verify_exact_in_route_rank_projection_packet",
                        "packet": packet.to_dict(),
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_exact_in_route_rank_projection_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_in_route_rank_projection_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_in_route_rank_projection_packet_payload,
                )

                ok, err = verify_exact_in_route_rank_projection_packet_payload(packet)
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_exact_in_route_rank_projection_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_in_route_true_key_interpretation_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_in = obj.get("amount_in")
                split_search_profile = str(obj.get("split_search_profile", "adaptive_v6")).strip()
                enable_mixed_direct_twohop_split = obj.get("enable_mixed_direct_twohop_split", False)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_amount_in"}, cors_origin=cors_origin)
                    return True
                if not split_search_profile:
                    self._write_json(400, {"ok": False, "error": "bad_split_search_profile"}, cors_origin=cors_origin)
                    return True
                if not isinstance(enable_mixed_direct_twohop_split, bool):
                    self._write_json(
                        400,
                        {"ok": False, "error": "bad_enable_mixed_direct_twohop_split"},
                        cors_origin=cors_origin,
                    )
                    return True

                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    build_exact_in_route_true_key_interpretation_packet_for_pools,
                )

                packet = build_exact_in_route_true_key_interpretation_packet_for_pools(
                    pools_by_id=pools_by_id,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amount_in),
                    split_search_profile=split_search_profile,
                    enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
                )
                if packet is None:
                    self._write_json(200, {"ok": False, "error": "no_route_candidates"}, cors_origin=cors_origin)
                    return True
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "packet_schema": "zenodex/exact-in-route-true-key-interpretation-packet/v1",
                        "verify_packet_endpoint": "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
                        "packet": packet.to_dict(),
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_exact_in_route_true_key_interpretation_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_in_route_true_key_interpretation_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_in_route_true_key_interpretation_packet_payload,
                )

                ok, err = verify_exact_in_route_true_key_interpretation_packet_payload(packet)
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_in_route_true_key_interpretation_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_settlement_spot_value_contract":
            settlement_obj = obj.get("settlement")
            asset_prices_obj = obj.get("asset_prices")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is None and price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is not None and (not isinstance(asset_prices_obj, dict) or not asset_prices_obj):
                self._write_json(400, {"ok": False, "error": "bad_asset_prices"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                settlement = _parse_settlement(settlement_obj)
                if price_attestation_obj is not None:
                    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPriceAttestation,
                    )
                    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
                        build_settlement_spot_value_contract_from_price_attestation,
                    )

                    price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_obj)
                    contract = build_settlement_spot_value_contract_from_price_attestation(
                        settlement=settlement,
                        price_attestation=price_attestation,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        allowed_signers=allowed_signers_obj,
                    )
                elif price_packet_obj is not None:
                    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPricePacket,
                    )
                    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
                        build_settlement_spot_value_contract_from_price_packet,
                    )

                    price_packet = SettlementSpotPricePacket.from_dict(price_packet_obj)
                    contract = build_settlement_spot_value_contract_from_price_packet(
                        settlement=settlement,
                        price_packet=price_packet,
                    )
                else:
                    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
                        build_settlement_spot_value_contract,
                    )

                    asset_prices: dict[str, int] = {}
                    for raw_asset, raw_price in asset_prices_obj.items():
                        asset = str(raw_asset).strip()
                        if not asset:
                            raise ValueError("asset_prices keys must be non-empty strings")
                        if not isinstance(raw_price, int) or isinstance(raw_price, bool) or raw_price < 0:
                            raise ValueError(f"asset price must be a non-negative int for {asset}")
                        asset_prices[asset] = int(raw_price)
                    contract = build_settlement_spot_value_contract(
                        settlement=settlement,
                        asset_prices=asset_prices,
                    )
                self._write_json(200, {"ok": True, "contract": contract.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_spot_value_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_spot_value_contract":
            settlement_obj = obj.get("settlement")
            asset_prices_obj = obj.get("asset_prices")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            contract_obj = obj.get("contract")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is None and price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is not None and (not isinstance(asset_prices_obj, dict) or not asset_prices_obj):
                self._write_json(400, {"ok": False, "error": "bad_asset_prices"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            if not isinstance(contract_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                settlement = _parse_settlement(settlement_obj)
                if price_attestation_obj is not None:
                    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_spot_value_contract_payload_from_price_attestation,
                    )

                    ok, err = verify_settlement_spot_value_contract_payload_from_price_attestation(
                        settlement=settlement,
                        price_attestation_payload=price_attestation_obj,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        contract_payload=contract_obj,
                        allowed_signers=allowed_signers_obj,
                    )
                elif price_packet_obj is not None:
                    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_spot_value_contract_payload_from_price_packet,
                    )

                    ok, err = verify_settlement_spot_value_contract_payload_from_price_packet(
                        settlement=settlement,
                        price_packet_payload=price_packet_obj,
                        contract_payload=contract_obj,
                    )
                else:
                    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_spot_value_contract_payload,
                    )

                    asset_prices: dict[str, int] = {}
                    for raw_asset, raw_price in asset_prices_obj.items():
                        asset = str(raw_asset).strip()
                        if not asset:
                            raise ValueError("asset_prices keys must be non-empty strings")
                        if not isinstance(raw_price, int) or isinstance(raw_price, bool) or raw_price < 0:
                            raise ValueError(f"asset price must be a non-negative int for {asset}")
                        asset_prices[asset] = int(raw_price)
                    ok, err = verify_settlement_spot_value_contract_payload(
                        settlement=settlement,
                        asset_prices=asset_prices,
                        contract_payload=contract_obj,
                    )
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_spot_value_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_settlement_lp_value_contract":
            settlement_obj = obj.get("settlement")
            asset_prices_obj = obj.get("asset_prices")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            lp_unit_values_obj = obj.get("lp_unit_values")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is None and price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is not None and (not isinstance(asset_prices_obj, dict) or not asset_prices_obj):
                self._write_json(400, {"ok": False, "error": "bad_asset_prices"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj:
                self._write_json(400, {"ok": False, "error": "bad_lp_unit_values"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                settlement = _parse_settlement(settlement_obj)
                lp_unit_values: dict[str, int] = {}
                for raw_pool_id, raw_unit_value in lp_unit_values_obj.items():
                    pool_id = str(raw_pool_id).strip()
                    if not pool_id:
                        raise ValueError("lp_unit_values keys must be non-empty strings")
                    if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
                        raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
                    lp_unit_values[pool_id] = int(raw_unit_value)

                if price_attestation_obj is not None:
                    from src.integration.settlement_lp_value_contract import (  # pylint: disable=import-outside-toplevel
                        build_settlement_lp_value_contract_from_price_attestation,
                    )
                    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPriceAttestation,
                    )

                    price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_obj)
                    contract = build_settlement_lp_value_contract_from_price_attestation(
                        settlement=settlement,
                        price_attestation=price_attestation,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        lp_unit_values=lp_unit_values,
                        allowed_signers=allowed_signers_obj,
                    )
                elif price_packet_obj is not None:
                    from src.integration.settlement_lp_value_contract import (  # pylint: disable=import-outside-toplevel
                        build_settlement_lp_value_contract_from_price_packet,
                    )
                    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPricePacket,
                    )

                    price_packet = SettlementSpotPricePacket.from_dict(price_packet_obj)
                    contract = build_settlement_lp_value_contract_from_price_packet(
                        settlement=settlement,
                        price_packet=price_packet,
                        lp_unit_values=lp_unit_values,
                    )
                else:
                    from src.integration.settlement_lp_value_contract import (  # pylint: disable=import-outside-toplevel
                        build_settlement_lp_value_contract,
                    )

                    asset_prices: dict[str, int] = {}
                    for raw_asset, raw_price in asset_prices_obj.items():
                        asset = str(raw_asset).strip()
                        if not asset:
                            raise ValueError("asset_prices keys must be non-empty strings")
                        if not isinstance(raw_price, int) or isinstance(raw_price, bool) or raw_price < 0:
                            raise ValueError(f"asset price must be a non-negative int for {asset}")
                        asset_prices[asset] = int(raw_price)
                    contract = build_settlement_lp_value_contract(
                        settlement=settlement,
                        asset_prices=asset_prices,
                        lp_unit_values=lp_unit_values,
                    )
                self._write_json(200, {"ok": True, "contract": contract.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_lp_value_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_lp_value_contract":
            settlement_obj = obj.get("settlement")
            asset_prices_obj = obj.get("asset_prices")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            lp_unit_values_obj = obj.get("lp_unit_values")
            contract_obj = obj.get("contract")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is None and price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if asset_prices_obj is not None and (not isinstance(asset_prices_obj, dict) or not asset_prices_obj):
                self._write_json(400, {"ok": False, "error": "bad_asset_prices"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj:
                self._write_json(400, {"ok": False, "error": "bad_lp_unit_values"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            if not isinstance(contract_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                settlement = _parse_settlement(settlement_obj)
                lp_unit_values: dict[str, int] = {}
                for raw_pool_id, raw_unit_value in lp_unit_values_obj.items():
                    pool_id = str(raw_pool_id).strip()
                    if not pool_id:
                        raise ValueError("lp_unit_values keys must be non-empty strings")
                    if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
                        raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
                    lp_unit_values[pool_id] = int(raw_unit_value)

                if price_attestation_obj is not None:
                    from src.integration.settlement_lp_value_contract import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_lp_value_contract_payload_from_price_attestation,
                    )

                    ok, err = verify_settlement_lp_value_contract_payload_from_price_attestation(
                        settlement=settlement,
                        price_attestation_payload=price_attestation_obj,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        lp_unit_values=lp_unit_values,
                        contract_payload=contract_obj,
                        allowed_signers=allowed_signers_obj,
                    )
                elif price_packet_obj is not None:
                    from src.integration.settlement_lp_value_contract import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_lp_value_contract_payload_from_price_packet,
                    )

                    ok, err = verify_settlement_lp_value_contract_payload_from_price_packet(
                        settlement=settlement,
                        price_packet_payload=price_packet_obj,
                        lp_unit_values=lp_unit_values,
                        contract_payload=contract_obj,
                    )
                else:
                    from src.integration.settlement_lp_value_contract import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_lp_value_contract_payload,
                    )

                    asset_prices: dict[str, int] = {}
                    for raw_asset, raw_price in asset_prices_obj.items():
                        asset = str(raw_asset).strip()
                        if not asset:
                            raise ValueError("asset_prices keys must be non-empty strings")
                        if not isinstance(raw_price, int) or isinstance(raw_price, bool) or raw_price < 0:
                            raise ValueError(f"asset price must be a non-negative int for {asset}")
                        asset_prices[asset] = int(raw_price)
                    ok, err = verify_settlement_lp_value_contract_payload(
                        settlement=settlement,
                        asset_prices=asset_prices,
                        lp_unit_values=lp_unit_values,
                        contract_payload=contract_obj,
                    )
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_lp_value_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_settlement_value_packet":
            settlement_obj = obj.get("settlement")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            lp_unit_values_obj = obj.get("lp_unit_values")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if lp_unit_values_obj is not None and (not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj):
                self._write_json(400, {"ok": False, "error": "bad_lp_unit_values"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel

                settlement = _parse_settlement(settlement_obj)
                lp_unit_values: dict[str, int] | None = None
                if lp_unit_values_obj is not None:
                    lp_unit_values = {}
                    for raw_pool_id, raw_unit_value in lp_unit_values_obj.items():
                        pool_id = str(raw_pool_id).strip()
                        if not pool_id:
                            raise ValueError("lp_unit_values keys must be non-empty strings")
                        if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
                            raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
                        lp_unit_values[pool_id] = int(raw_unit_value)

                if price_attestation_obj is not None:
                    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPriceAttestation,
                    )
                    from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
                        build_settlement_value_packet_from_price_attestation,
                    )

                    price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_obj)
                    packet = build_settlement_value_packet_from_price_attestation(
                        settlement=settlement,
                        price_attestation=price_attestation,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        lp_unit_values=lp_unit_values,
                        allowed_signers=allowed_signers_obj,
                    )
                else:
                    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPricePacket,
                    )
                    from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
                        build_settlement_value_packet_from_price_packet,
                    )

                    price_packet = SettlementSpotPricePacket.from_dict(price_packet_obj)
                    packet = build_settlement_value_packet_from_price_packet(
                        settlement=settlement,
                        price_packet=price_packet,
                        lp_unit_values=lp_unit_values,
                    )
                self._write_json(200, {"ok": True, "packet": packet.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_value_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_value_packet":
            settlement_obj = obj.get("settlement")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            lp_unit_values_obj = obj.get("lp_unit_values")
            packet_obj = obj.get("packet")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if lp_unit_values_obj is not None and (not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj):
                self._write_json(400, {"ok": False, "error": "bad_lp_unit_values"}, cors_origin=cors_origin)
                return True
            if not isinstance(packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel

                settlement = _parse_settlement(settlement_obj)
                lp_unit_values: dict[str, int] | None = None
                if lp_unit_values_obj is not None:
                    lp_unit_values = {}
                    for raw_pool_id, raw_unit_value in lp_unit_values_obj.items():
                        pool_id = str(raw_pool_id).strip()
                        if not pool_id:
                            raise ValueError("lp_unit_values keys must be non-empty strings")
                        if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
                            raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
                        lp_unit_values[pool_id] = int(raw_unit_value)

                if price_attestation_obj is not None:
                    from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_value_packet_payload_from_price_attestation,
                    )

                    ok, err = verify_settlement_value_packet_payload_from_price_attestation(
                        settlement=settlement,
                        price_attestation_payload=price_attestation_obj,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        packet_payload=packet_obj,
                        lp_unit_values=lp_unit_values,
                        allowed_signers=allowed_signers_obj,
                    )
                else:
                    from src.integration.settlement_value_packet import (  # pylint: disable=import-outside-toplevel
                        verify_settlement_value_packet_payload_from_price_packet,
                    )

                    ok, err = verify_settlement_value_packet_payload_from_price_packet(
                        settlement=settlement,
                        price_packet_payload=price_packet_obj,
                        packet_payload=packet_obj,
                        lp_unit_values=lp_unit_values,
                    )
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_value_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_settlement_endogenous_lp_value_packet":
            settlement_obj = obj.get("settlement")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            pool_snapshots_obj = obj.get("pool_snapshots")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if not isinstance(pool_snapshots_obj, list) or not pool_snapshots_obj:
                self._write_json(400, {"ok": False, "error": "bad_pool_snapshots"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
                    _pool_from_dict,
                    build_settlement_endogenous_lp_value_packet_from_price_attestation,
                    build_settlement_endogenous_lp_value_packet_from_price_packet,
                )

                settlement = _parse_settlement(settlement_obj)
                pool_snapshots = tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_obj)
                if price_attestation_obj is not None:
                    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPriceAttestation,
                    )

                    price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_obj)
                    packet = build_settlement_endogenous_lp_value_packet_from_price_attestation(
                        settlement=settlement,
                        price_attestation=price_attestation,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        pool_snapshots=pool_snapshots,
                        allowed_signers=allowed_signers_obj,
                    )
                else:
                    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPricePacket,
                    )

                    price_packet = SettlementSpotPricePacket.from_dict(price_packet_obj)
                    packet = build_settlement_endogenous_lp_value_packet_from_price_packet(
                        settlement=settlement,
                        price_packet=price_packet,
                        pool_snapshots=pool_snapshots,
                    )
                self._write_json(200, {"ok": True, "packet": packet.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_endogenous_lp_value_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_endogenous_lp_value_packet":
            settlement_obj = obj.get("settlement")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            pool_snapshots_obj = obj.get("pool_snapshots")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            packet_obj = obj.get("packet")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if not isinstance(pool_snapshots_obj, list) or not pool_snapshots_obj:
                self._write_json(400, {"ok": False, "error": "bad_pool_snapshots"}, cors_origin=cors_origin)
                return True
            if not isinstance(packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
                    verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation,
                    verify_settlement_endogenous_lp_value_packet_payload_from_price_packet,
                )

                settlement = _parse_settlement(settlement_obj)
                if price_attestation_obj is not None:
                    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation(
                        settlement=settlement,
                        price_attestation_payload=price_attestation_obj,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        pool_snapshots_payload=pool_snapshots_obj,
                        packet_payload=packet_obj,
                        allowed_signers=allowed_signers_obj,
                    )
                else:
                    ok, err = verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
                        settlement=settlement,
                        price_packet_payload=price_packet_obj,
                        pool_snapshots_payload=pool_snapshots_obj,
                        packet_payload=packet_obj,
                    )
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_endogenous_lp_value_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_settlement_feature_extension_packet":
            feature_extension_inputs_obj = obj.get("feature_extension_inputs")
            try:
                from src.integration.settlement_feature_extension_packet import (  # pylint: disable=import-outside-toplevel
                    build_settlement_feature_extension_packet,
                )

                feature_extension_inputs = _parse_settlement_feature_extension_inputs_payload(
                    feature_extension_inputs_obj
                )
                packet = build_settlement_feature_extension_packet(feature_extension_inputs)
                self._write_json(200, {"ok": True, "packet": packet.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_feature_extension_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_feature_extension_packet":
            feature_extension_inputs_obj = obj.get("feature_extension_inputs")
            packet_obj = obj.get("packet")
            if not isinstance(packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.settlement_feature_extension_packet import (  # pylint: disable=import-outside-toplevel
                    verify_settlement_feature_extension_packet_payload,
                )

                ok, err = verify_settlement_feature_extension_packet_payload(
                    inputs_payload=feature_extension_inputs_obj,
                    packet_payload=packet_obj,
                )
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_feature_extension_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_settlement_end_to_end_certificate_packet":
            settlement_obj = obj.get("settlement")
            proof_flags_obj = obj.get("proof_flags")
            price_history_obj = obj.get("price_history")
            feature_extension_inputs_obj = obj.get("feature_extension_inputs")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            pool_snapshots_obj = obj.get("pool_snapshots")
            lp_unit_values_obj = obj.get("lp_unit_values")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if pool_snapshots_obj is not None and (not isinstance(pool_snapshots_obj, list) or not pool_snapshots_obj):
                self._write_json(400, {"ok": False, "error": "bad_pool_snapshots"}, cors_origin=cors_origin)
                return True
            if lp_unit_values_obj is not None and (not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj):
                self._write_json(400, {"ok": False, "error": "bad_lp_unit_values"}, cors_origin=cors_origin)
                return True
            if pool_snapshots_obj is not None and lp_unit_values_obj is not None:
                self._write_json(400, {"ok": False, "error": "conflicting_value_mode_inputs"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
                    build_settlement_end_to_end_certificate_packet_from_price_attestation,
                    build_settlement_end_to_end_certificate_packet_from_price_packet,
                )
                from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
                    _pool_from_dict,
                )

                settlement = _parse_settlement(settlement_obj)
                proof_flags = _parse_settlement_proof_flags_payload(proof_flags_obj)
                price_history = _parse_price_history_payload(price_history_obj)
                feature_extension_inputs = _parse_settlement_feature_extension_inputs_payload(
                    feature_extension_inputs_obj
                )
                pool_snapshots = None if pool_snapshots_obj is None else tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_obj)
                lp_unit_values: dict[str, int] | None = None
                if lp_unit_values_obj is not None:
                    lp_unit_values = {}
                    for raw_pool_id, raw_unit_value in lp_unit_values_obj.items():
                        pool_id = str(raw_pool_id).strip()
                        if not pool_id:
                            raise ValueError("lp_unit_values keys must be non-empty strings")
                        if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
                            raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
                        lp_unit_values[pool_id] = int(raw_unit_value)

                if price_attestation_obj is not None:
                    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPriceAttestation,
                    )

                    price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_obj)
                    packet = build_settlement_end_to_end_certificate_packet_from_price_attestation(
                        settlement=settlement,
                        proof_flags=proof_flags,
                        price_history=price_history,
                        feature_extension_inputs=feature_extension_inputs,
                        price_attestation=price_attestation,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        lp_unit_values=lp_unit_values,
                        pool_snapshots=pool_snapshots,
                        allowed_signers=allowed_signers_obj,
                    )
                else:
                    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                        SettlementSpotPricePacket,
                    )

                    price_packet = SettlementSpotPricePacket.from_dict(price_packet_obj)
                    packet = build_settlement_end_to_end_certificate_packet_from_price_packet(
                        settlement=settlement,
                        proof_flags=proof_flags,
                        price_history=price_history,
                        feature_extension_inputs=feature_extension_inputs,
                        price_packet=price_packet,
                        lp_unit_values=lp_unit_values,
                        pool_snapshots=pool_snapshots,
                    )
                self._write_json(200, {"ok": True, "packet": packet.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_end_to_end_certificate_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_end_to_end_certificate_packet":
            settlement_obj = obj.get("settlement")
            proof_flags_obj = obj.get("proof_flags")
            price_history_obj = obj.get("price_history")
            feature_extension_inputs_obj = obj.get("feature_extension_inputs")
            price_packet_obj = obj.get("price_packet")
            price_attestation_obj = obj.get("price_attestation")
            pool_snapshots_obj = obj.get("pool_snapshots")
            lp_unit_values_obj = obj.get("lp_unit_values")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            packet_obj = obj.get("packet")
            if not isinstance(settlement_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_settlement"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is None and price_attestation_obj is None:
                self._write_json(400, {"ok": False, "error": "missing_price_input"}, cors_origin=cors_origin)
                return True
            if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_price_attestation"}, cors_origin=cors_origin)
                return True
            if pool_snapshots_obj is not None and (not isinstance(pool_snapshots_obj, list) or not pool_snapshots_obj):
                self._write_json(400, {"ok": False, "error": "bad_pool_snapshots"}, cors_origin=cors_origin)
                return True
            if lp_unit_values_obj is not None and (not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj):
                self._write_json(400, {"ok": False, "error": "bad_lp_unit_values"}, cors_origin=cors_origin)
                return True
            if pool_snapshots_obj is not None and lp_unit_values_obj is not None:
                self._write_json(400, {"ok": False, "error": "conflicting_value_mode_inputs"}, cors_origin=cors_origin)
                return True
            if not isinstance(packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            if price_attestation_obj is not None:
                if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                    self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                    return True
                if (
                    not isinstance(max_attestation_age_epochs, int)
                    or isinstance(max_attestation_age_epochs, bool)
                    or max_attestation_age_epochs < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                    return True
                if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                    self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                    return True
            try:
                from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel
                from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
                    verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation,
                    verify_settlement_end_to_end_certificate_packet_payload_from_price_packet,
                )

                settlement = _parse_settlement(settlement_obj)
                proof_flags = _parse_settlement_proof_flags_payload(proof_flags_obj)
                price_history = _parse_price_history_payload(price_history_obj)
                lp_unit_values: dict[str, int] | None = None
                if lp_unit_values_obj is not None:
                    lp_unit_values = {}
                    for raw_pool_id, raw_unit_value in lp_unit_values_obj.items():
                        pool_id = str(raw_pool_id).strip()
                        if not pool_id:
                            raise ValueError("lp_unit_values keys must be non-empty strings")
                        if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
                            raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
                        lp_unit_values[pool_id] = int(raw_unit_value)

                if price_attestation_obj is not None:
                    ok, err = verify_settlement_end_to_end_certificate_packet_payload_from_price_attestation(
                        settlement=settlement,
                        proof_flags=proof_flags,
                        price_history=price_history,
                        feature_extension_inputs_payload=feature_extension_inputs_obj,
                        price_attestation_payload=price_attestation_obj,
                        consumer_now_epoch=int(consumer_now_epoch),
                        max_attestation_age_epochs=int(max_attestation_age_epochs),
                        packet_payload=packet_obj,
                        lp_unit_values=lp_unit_values,
                        pool_snapshots_payload=pool_snapshots_obj,
                        allowed_signers=allowed_signers_obj,
                    )
                else:
                    ok, err = verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
                        settlement=settlement,
                        proof_flags=proof_flags,
                        price_history=price_history,
                        feature_extension_inputs_payload=feature_extension_inputs_obj,
                        price_packet_payload=price_packet_obj,
                        packet_payload=packet_obj,
                        lp_unit_values=lp_unit_values,
                        pool_snapshots_payload=pool_snapshots_obj,
                    )
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_end_to_end_certificate_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True


        from src.integration.api_server_settlement_witness_routes import (  # pylint: disable=import-outside-toplevel
            maybe_handle_settlement_witness_lifecycle_route,
        )

        if maybe_handle_settlement_witness_lifecycle_route(
            path=path,
            obj=obj,
            write_json=lambda status, body: self._write_json(status, body, cors_origin=cors_origin),
            parse_pools=_parse_pools,
            parse_settlement_proof_flags_payload=_parse_settlement_proof_flags_payload,
            parse_price_history_payload=_parse_price_history_payload,
            parse_settlement_feature_extension_inputs_payload=_parse_settlement_feature_extension_inputs_payload,
        ):
            return True

        if path == "/api/dex/build_settlement_spot_price_packet":
            entries_obj = obj.get("entries")
            now_epoch = obj.get("now_epoch")
            max_staleness_epochs = obj.get("max_staleness_epochs")
            cross_module_sync_required = obj.get("cross_module_sync_required", False)
            cross_module_sync_contract = obj.get("cross_module_sync_contract")
            if not isinstance(entries_obj, list) or not entries_obj:
                self._write_json(400, {"ok": False, "error": "bad_entries"}, cors_origin=cors_origin)
                return True
            if not isinstance(now_epoch, int) or isinstance(now_epoch, bool) or now_epoch < 0:
                self._write_json(400, {"ok": False, "error": "bad_now_epoch"}, cors_origin=cors_origin)
                return True
            if not isinstance(max_staleness_epochs, int) or isinstance(max_staleness_epochs, bool) or max_staleness_epochs < 0:
                self._write_json(400, {"ok": False, "error": "bad_max_staleness_epochs"}, cors_origin=cors_origin)
                return True
            if not isinstance(cross_module_sync_required, bool):
                self._write_json(400, {"ok": False, "error": "bad_cross_module_sync_required"}, cors_origin=cors_origin)
                return True
            if cross_module_sync_contract is not None and not isinstance(cross_module_sync_contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_cross_module_sync_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                    SettlementSpotPriceEntry,
                    build_settlement_spot_price_packet,
                )

                entries = tuple(SettlementSpotPriceEntry.from_dict(entry) for entry in entries_obj)
                packet = build_settlement_spot_price_packet(
                    entries=entries,
                    now_epoch=int(now_epoch),
                    max_staleness_epochs=int(max_staleness_epochs),
                    cross_module_sync_required=bool(cross_module_sync_required),
                    cross_module_sync_contract=cross_module_sync_contract,
                )
                self._write_json(200, {"ok": True, "packet": packet.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_spot_price_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_spot_price_packet":
            packet_obj = obj.get("packet")
            if not isinstance(packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                    verify_settlement_spot_price_packet_payload,
                )

                ok, err = verify_settlement_spot_price_packet_payload(packet_obj)
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_spot_price_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_settlement_spot_price_attestation":
            packet_obj = obj.get("packet")
            signer_privkey = obj.get("signer_privkey")
            if not isinstance(packet_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            if not isinstance(signer_privkey, (str, int)):
                self._write_json(400, {"ok": False, "error": "bad_signer_privkey"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
                    build_settlement_spot_price_attestation,
                )
                from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
                    SettlementSpotPricePacket,
                )

                packet = SettlementSpotPricePacket.from_dict(packet_obj)
                attestation = build_settlement_spot_price_attestation(
                    packet=packet,
                    signer_privkey=signer_privkey,
                )
                self._write_json(200, {"ok": True, "attestation": attestation.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_settlement_spot_price_attestation_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_settlement_spot_price_attestation":
            attestation_obj = obj.get("attestation")
            consumer_now_epoch = obj.get("consumer_now_epoch")
            max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
            allowed_signers_obj = obj.get("allowed_signers")
            if not isinstance(attestation_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_attestation"}, cors_origin=cors_origin)
                return True
            if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
                self._write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"}, cors_origin=cors_origin)
                return True
            if (
                not isinstance(max_attestation_age_epochs, int)
                or isinstance(max_attestation_age_epochs, bool)
                or max_attestation_age_epochs < 0
            ):
                self._write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"}, cors_origin=cors_origin)
                return True
            if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
                self._write_json(400, {"ok": False, "error": "bad_allowed_signers"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
                    verify_settlement_spot_price_attestation_payload,
                )

                ok, err = verify_settlement_spot_price_attestation_payload(
                    payload=attestation_obj,
                    consumer_now_epoch=int(consumer_now_epoch),
                    max_attestation_age_epochs=int(max_attestation_age_epochs),
                    allowed_signers=allowed_signers_obj,
                )
                self._write_json(200, {"ok": bool(ok), "error": err}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_settlement_spot_price_attestation_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_route_certificate":
            quotes_obj = obj.get("quotes")
            if not isinstance(quotes_obj, list) or not quotes_obj:
                self._write_json(400, {"ok": False, "error": "bad_quotes"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    build_exact_out_route_canonical_certificate,
                )

                quotes = tuple(_exact_out_split_quote_from_dict(quote_obj) for quote_obj in quotes_obj)
                certificate = build_exact_out_route_canonical_certificate(quotes)
                self._write_json(200, {"ok": True, "certificate": certificate.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "bad_exact_out_certificate_request", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/audit_exact_out_two_pool_canonicality":
            try:
                pools_by_id = _parse_pools()
                if len(pools_by_id) != 2:
                    self._write_json(400, {"ok": False, "error": "expected_exactly_two_pools"}, cors_origin=cors_origin)
                    return True
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                brute_force_max = obj.get("brute_force_max")
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                if not isinstance(amount_out_total, int) or isinstance(amount_out_total, bool) or amount_out_total <= 0:
                    self._write_json(400, {"ok": False, "error": "bad_amount_out_total"}, cors_origin=cors_origin)
                    return True
                if brute_force_max is not None and (
                    not isinstance(brute_force_max, int) or isinstance(brute_force_max, bool) or brute_force_max < 0
                ):
                    self._write_json(400, {"ok": False, "error": "bad_brute_force_max"}, cors_origin=cors_origin)
                    return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    audit_exact_out_two_pool_runtime_canonicality,
                )

                pools = list(pools_by_id.values())
                audit = audit_exact_out_two_pool_runtime_canonicality(
                    pools[0],
                    pools[1],
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    brute_force_max=(None if brute_force_max is None else int(brute_force_max)),
                )
                self._write_json(200, {"ok": True, "audit": audit.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "audit_exact_out_two_pool_canonicality_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/audit_exact_out_many_pool_canonicality":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    audit_exact_out_many_pool_runtime_canonicality,
                )

                audit = audit_exact_out_many_pool_runtime_canonicality(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(200, {"ok": True, "audit": audit.to_dict()}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "audit_exact_out_many_pool_canonicality_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_candidate_domain_contract":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA,
                    build_exact_out_many_pool_candidate_domain_contract,
                )

                contract = build_exact_out_many_pool_candidate_domain_contract(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "contract": contract.to_dict(),
                        "contract_schema": EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA,
                        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_candidate_domain_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_prefilter_contract":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA,
                    build_exact_out_many_pool_prefilter_contract,
                )

                contract = build_exact_out_many_pool_prefilter_contract(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "contract": contract.to_dict(),
                        "contract_schema": EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA,
                        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_prefilter_contract",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_prefilter_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA,
                    build_exact_out_many_pool_repaired_prefilter_contract,
                )

                contract = build_exact_out_many_pool_repaired_prefilter_contract(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "contract": contract.to_dict(),
                        "contract_schema": EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA,
                        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_repaired_prefilter_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA,
                    build_exact_out_many_pool_repaired_selected_domain_oracle_contract,
                )

                contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "contract": contract.to_dict(),
                        "contract_schema": EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA,
                        "quote_endpoint": "/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
                        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool_repaired_selected_domain":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    quote_exact_out_many_pool_repaired_selected_domain,
                )

                quote, err, contract = quote_exact_out_many_pool_repaired_selected_domain(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                contract_payload = contract.to_dict()
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
                    "audit_pool_ids_match_repaired_selected_pool_ids": contract_payload[
                        "audit_pool_ids_match_repaired_selected_pool_ids"
                    ],
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
                    "replacement_quote_matches_full_canonical": contract_payload[
                        "replacement_quote_matches_full_canonical"
                    ],
                }
                if quote is not None:
                    payload["quote"] = contract_payload["repaired_selected_domain_runtime_quote"]
                else:
                    payload["error"] = str(err or "many_pool_repaired_selected_domain_unavailable")
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "quote_exact_out_many_pool_repaired_selected_domain_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool_repaired_advisory":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    quote_exact_out_many_pool_repaired_advisory,
                )

                quote, err, packet = quote_exact_out_many_pool_repaired_advisory(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                runtime_quote_payload = packet.to_dict()["runtime_quote"]
                advisory_quote_payload = packet.to_dict()["advisory_quote"]
                repaired_projection_cover = packet.to_dict()["projection_cover_audit"]
                runtime_projected_path = _projected_path_from_exact_out_quote_payload(runtime_quote_payload)
                advisory_projected_path = _projected_path_from_exact_out_quote_payload(advisory_quote_payload)
                repaired_canonical_projected_path = (
                    None
                    if repaired_projection_cover is None
                    else repaired_projection_cover["canonical_quote_projected_path"]
                )
                payload = {
                    "ok": bool(quote is not None),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet",
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
                    "runtime_quote": runtime_quote_payload,
                    "runtime_matches_advisory": bool(packet.runtime_matches_advisory),
                    "runtime_projected_path": runtime_projected_path,
                    "advisory_projected_path": advisory_projected_path,
                    "repaired_projection_cover_available": bool(repaired_projection_cover is not None),
                    "repaired_projection_cover_holds": (
                        None if repaired_projection_cover is None else bool(repaired_projection_cover["projection_cover_holds"])
                    ),
                    "repaired_canonical_projected_path": repaired_canonical_projected_path,
                    "effective_projection_cover_side": "repaired" if quote is not None else None,
                    "effective_projection_cover_holds": (
                        None if repaired_projection_cover is None else bool(repaired_projection_cover["projection_cover_holds"])
                    ),
                    "effective_canonical_projected_path": repaired_canonical_projected_path,
                    "effective_quote_projected_path": advisory_projected_path,
                    "effective_quote_matches_canonical_projected_path": (
                        None
                        if advisory_projected_path is None or repaired_canonical_projected_path is None
                        else bool(advisory_projected_path == repaired_canonical_projected_path)
                    ),
                }
                if quote is not None:
                    payload["quote"] = advisory_quote_payload
                else:
                    payload["error"] = str(err or "many_pool_repaired_prefilter_contract_not_ok")
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "quote_exact_out_many_pool_repaired_advisory_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
                    quote_exact_out_many_pool_repaired_full_domain_certified,
                )

                quote, err, packet = quote_exact_out_many_pool_repaired_full_domain_certified(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                payload = {
                    "ok": bool(quote is not None),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
                    "quote_policy": "repaired_full_domain_certified_v1",
                    "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet",
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
                    "runtime_quote": packet.repaired_packet.to_dict()["runtime_quote"],
                    "full_domain_canonical_quote": packet.to_dict()["full_domain_canonical_quote"],
                    "repaired_matches_full_canonical": bool(packet.repaired_matches_full_canonical),
                    "full_domain_candidate_count": int(packet.full_domain_candidate_count),
                    "full_domain_feasible_pool_ids": [str(pool_id) for pool_id in packet.full_domain_feasible_pool_ids],
                }
                if quote is not None:
                    payload["quote"] = packet.to_dict()["repaired_quote"]
                else:
                    payload["error"] = str(err or "many_pool_repaired_advisory_not_full_domain_canonical")
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "quote_exact_out_many_pool_repaired_full_domain_certified_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool_bounded_advisory":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    quote_exact_out_many_pool_bounded_advisory,
                )

                quote, err, packet = quote_exact_out_many_pool_bounded_advisory(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                packet_payload = packet.to_dict()
                selected_projection_cover = packet_payload["workaround_packet"]["oracle_contract"]["audit"]["projection_cover_audit"]
                repaired_projection_cover = packet_payload["workaround_packet"]["repaired_packet"]["projection_cover_audit"]
                runtime_quote_payload = packet_payload["workaround_packet"]["oracle_contract"]["audit"]["runtime_quote"]
                advisory_quote_payload = packet_payload["advisory_quote"]
                runtime_projected_path = _projected_path_from_exact_out_quote_payload(runtime_quote_payload)
                advisory_projected_path = _projected_path_from_exact_out_quote_payload(advisory_quote_payload)
                selected_canonical_projected_path = (
                    None if selected_projection_cover is None else selected_projection_cover["canonical_quote_projected_path"]
                )
                repaired_canonical_projected_path = (
                    None if repaired_projection_cover is None else repaired_projection_cover["canonical_quote_projected_path"]
                )
                if packet.quote_source == "selected_domain_runtime":
                    effective_projection_cover_side = "selected_domain"
                    effective_projection_cover_holds = (
                        None if selected_projection_cover is None else bool(selected_projection_cover["projection_cover_holds"])
                    )
                    effective_canonical_projected_path = selected_canonical_projected_path
                    effective_quote_projected_path = runtime_projected_path
                elif packet.quote_source == "repaired_bounded_advisory":
                    effective_projection_cover_side = "repaired"
                    effective_projection_cover_holds = (
                        None if repaired_projection_cover is None else bool(repaired_projection_cover["projection_cover_holds"])
                    )
                    effective_canonical_projected_path = repaired_canonical_projected_path
                    effective_quote_projected_path = advisory_projected_path
                else:
                    effective_projection_cover_side = None
                    effective_projection_cover_holds = None
                    effective_canonical_projected_path = None
                    effective_quote_projected_path = None
                payload = {
                    "ok": bool(quote is not None),
                    "packet": packet_payload,
                    "packet_schema": EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet",
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
                    "runtime_quote": runtime_quote_payload,
                    "quote_source": packet.quote_source,
                    "repaired_advisory_available": bool(packet.repaired_advisory_available),
                    "quote_matches_runtime": bool(packet.quote_matches_runtime),
                    "quote_matches_repaired_advisory": bool(packet.quote_matches_repaired_advisory),
                    "runtime_projected_path": runtime_projected_path,
                    "advisory_projected_path": advisory_projected_path,
                    "selected_domain_projection_cover_available": bool(selected_projection_cover is not None),
                    "selected_domain_projection_cover_holds": (
                        None if selected_projection_cover is None else bool(selected_projection_cover["projection_cover_holds"])
                    ),
                    "selected_domain_canonical_projected_path": selected_canonical_projected_path,
                    "selected_runtime_matches_selected_canonical_projected_path": (
                        None
                        if runtime_projected_path is None or selected_canonical_projected_path is None
                        else bool(runtime_projected_path == selected_canonical_projected_path)
                    ),
                    "repaired_projection_cover_available": bool(repaired_projection_cover is not None),
                    "repaired_projection_cover_holds": (
                        None if repaired_projection_cover is None else bool(repaired_projection_cover["projection_cover_holds"])
                    ),
                    "repaired_canonical_projected_path": repaired_canonical_projected_path,
                    "advisory_matches_repaired_canonical_projected_path": (
                        None
                        if advisory_projected_path is None or repaired_canonical_projected_path is None
                        else bool(advisory_projected_path == repaired_canonical_projected_path)
                    ),
                    "effective_projection_cover_side": effective_projection_cover_side,
                    "effective_projection_cover_holds": effective_projection_cover_holds,
                    "effective_canonical_projected_path": effective_canonical_projected_path,
                    "effective_quote_projected_path": effective_quote_projected_path,
                    "effective_quote_matches_canonical_projected_path": (
                        None
                        if effective_quote_projected_path is None or effective_canonical_projected_path is None
                        else bool(effective_quote_projected_path == effective_canonical_projected_path)
                    ),
                }
                if quote is not None:
                    payload["quote"] = advisory_quote_payload
                else:
                    payload["error"] = str(err or "many_pool_bounded_advisory_unavailable")
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "quote_exact_out_many_pool_bounded_advisory_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    quote_exact_out_many_pool_default,
                )

                quote, err, packet = quote_exact_out_many_pool_default(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                packet_payload = packet.to_dict()
                payload = {
                    "ok": bool(quote is not None),
                    "quote_policy": "certified_advisory_v1",
                    "packet": packet_payload,
                    "packet_schema": packet_payload["schema"],
                    "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_default_packet",
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_default_packet",
                    "runtime_quote": packet_payload["selected_domain_runtime_quote"],
                    "quote_source": packet_payload["effective_quote_source"],
                    "repaired_advisory_available": bool(packet.advisory_packet.repaired_advisory_available),
                    "quote_matches_runtime": bool(packet_payload["effective_quote_matches_selected_runtime_quote"]),
                    "quote_matches_repaired_advisory": bool(packet_payload["effective_quote_matches_repaired_advisory_quote"]),
                    "repaired_full_domain_packet_ok": bool(packet_payload["repaired_full_domain_packet_ok"]),
                    "repaired_quote_matches_full_domain_canonical": bool(
                        packet_payload["repaired_quote_matches_full_domain_canonical"]
                    ),
                    "repaired_full_domain_feasible_pool_ids": packet_payload["repaired_full_domain_feasible_pool_ids"],
                    "repaired_full_domain_candidate_count": packet_payload["repaired_full_domain_candidate_count"],
                    "repaired_full_domain_canonical_quote": packet_payload["repaired_full_domain_canonical_quote"],
                    "effective_quote_matches_full_domain_canonical": packet_payload[
                        "effective_quote_matches_full_domain_canonical"
                    ],
                    "repaired_key_cover_packet_ok": bool(packet_payload["repaired_key_cover_packet_ok"]),
                    "repaired_selected_keys_subset_full_keys": bool(
                        packet_payload["repaired_selected_keys_subset_full_keys"]
                    ),
                    "repaired_key_cover_holds": bool(packet_payload["repaired_key_cover_holds"]),
                    "repaired_selected_domain_canonical_matches_full_domain_canonical": bool(
                        packet_payload["repaired_selected_domain_canonical_matches_full_domain_canonical"]
                    ),
                    "repaired_key_cover_witness_count": int(packet_payload["repaired_key_cover_witness_count"]),
                    "repaired_key_cover_interpretation_packet_ok": bool(
                        packet_payload["repaired_key_cover_interpretation_packet_ok"]
                    ),
                    "repaired_key_cover_selected_winner_index_in_range": bool(
                        packet_payload["repaired_key_cover_selected_winner_index_in_range"]
                    ),
                    "repaired_key_cover_selected_winner_matches_certificate": bool(
                        packet_payload["repaired_key_cover_selected_winner_matches_certificate"]
                    ),
                    "repaired_key_cover_selected_winner_key_minimal": bool(
                        packet_payload["repaired_key_cover_selected_winner_key_minimal"]
                    ),
                    "repaired_key_cover_witness_indices_in_range": bool(
                        packet_payload["repaired_key_cover_witness_indices_in_range"]
                    ),
                    "repaired_key_cover_witness_coverage_complete": bool(
                        packet_payload["repaired_key_cover_witness_coverage_complete"]
                    ),
                    "repaired_key_cover_witness_keys_match_candidates": bool(
                        packet_payload["repaired_key_cover_witness_keys_match_candidates"]
                    ),
                    "repaired_key_cover_witness_domination_holds": bool(
                        packet_payload["repaired_key_cover_witness_domination_holds"]
                    ),
                    "effective_quote": packet_payload["effective_quote"],
                    "selected_runtime_quotes_agree": bool(packet.selected_runtime_quotes_agree),
                    "selected_domain_runtime_projected_path": packet_payload["selected_domain_runtime_projected_path"],
                    "advisory_projected_path": packet_payload["advisory_projected_path"],
                    "selected_domain_projection_cover_available": packet_payload["selected_domain_projection_cover_available"],
                    "selected_domain_projection_cover_holds": packet_payload["selected_domain_projection_cover_holds"],
                    "selected_domain_canonical_projected_path": packet_payload["selected_domain_canonical_projected_path"],
                    "selected_runtime_matches_selected_canonical_projected_path": packet_payload[
                        "selected_runtime_matches_selected_canonical_projected_path"
                    ],
                    "repaired_projection_cover_available": packet_payload["repaired_projection_cover_available"],
                    "repaired_projection_cover_holds": packet_payload["repaired_projection_cover_holds"],
                    "repaired_canonical_projected_path": packet_payload["repaired_canonical_projected_path"],
                    "advisory_matches_repaired_canonical_projected_path": packet_payload[
                        "advisory_matches_repaired_canonical_projected_path"
                    ],
                    "effective_projection_cover_side": packet_payload["effective_projection_cover_side"],
                    "effective_projection_cover_holds": packet_payload["effective_projection_cover_holds"],
                    "effective_canonical_projected_path": packet_payload["effective_canonical_projected_path"],
                    "effective_quote_projected_path": packet_payload["effective_quote_projected_path"],
                    "effective_quote_matches_canonical_projected_path": packet_payload[
                        "effective_quote_matches_canonical_projected_path"
                    ],
                }
                if quote is not None:
                    payload["quote"] = packet_payload["effective_quote"]
                else:
                    payload["error"] = str(err or "many_pool_certified_advisory_unavailable")
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "quote_exact_out_many_pool_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool_adaptive":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    quote_exact_out_many_pool_adaptive,
                )

                quote, err, packet = quote_exact_out_many_pool_adaptive(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                packet_payload = packet.to_dict()
                payload = {
                    "ok": bool(quote is not None),
                    "quote_policy": "adaptive_liveness_v1",
                    "packet": packet_payload,
                    "packet_schema": packet_payload["schema"],
                    "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet",
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
                    "audited_bounds_contract_ok": bool(packet_payload["audited_bounds_contract_ok"]),
                    "default_packet_ok": bool(packet_payload["default_packet_ok"]),
                    "default_effective_quote_source": packet_payload["default_effective_quote_source"],
                    "repaired_full_domain_packet_ok": bool(packet_payload["repaired_full_domain_packet_ok"]),
                    "repaired_quote_matches_full_domain_canonical": bool(
                        packet_payload["repaired_quote_matches_full_domain_canonical"]
                    ),
                    "cheap_path_attempted": bool(packet_payload["cheap_path_attempted"]),
                    "cheap_path_success": bool(packet_payload["cheap_path_success"]),
                    "fallback_required": bool(packet_payload["fallback_required"]),
                    "fallback_attempted": bool(packet_payload["fallback_attempted"]),
                    "fallback_available": bool(packet_payload["fallback_available"]),
                    "fallback_success": bool(packet_payload["fallback_success"]),
                    "returned_success": bool(packet_payload["returned_success"]),
                    "explicit_failure": bool(packet_payload["explicit_failure"]),
                    "no_spurious_failure": bool(packet_payload["no_spurious_failure"]),
                    "packet_ok": bool(packet_payload["packet_ok"]),
                    "liveness_ok": bool(packet_payload["liveness_ok"]),
                    "quote_source": packet_payload["effective_quote_source"],
                    "effective_quote": packet_payload["effective_quote"],
                    "failure_reason": packet_payload["failure_reason"],
                    "nested_error": packet_payload["nested_error"],
                }
                if quote is not None:
                    payload["quote"] = packet_payload["effective_quote"]
                else:
                    payload["error"] = str(err or packet_payload["failure_reason"] or "many_pool_adaptive_unavailable")
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "quote_exact_out_many_pool_adaptive_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool_certified_advisory":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    quote_exact_out_many_pool_certified_advisory,
                )

                quote, err, packet = quote_exact_out_many_pool_certified_advisory(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                packet_payload = packet.to_dict()
                payload = {
                    "ok": bool(quote is not None),
                    "quote_policy": "certified_advisory_v1",
                    "packet": packet_payload,
                    "packet_schema": packet_payload["schema"],
                    "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_certified_advisory_packet",
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
                    "quote_source": packet_payload["effective_quote_source"],
                    "repaired_advisory_available": bool(packet.advisory_packet.repaired_advisory_available),
                    "quote_matches_runtime": bool(packet_payload["effective_quote_matches_selected_runtime_quote"]),
                    "quote_matches_repaired_advisory": bool(packet_payload["effective_quote_matches_repaired_advisory_quote"]),
                    "repaired_full_domain_packet_ok": bool(packet_payload["repaired_full_domain_packet_ok"]),
                    "repaired_quote_matches_full_domain_canonical": bool(
                        packet_payload["repaired_quote_matches_full_domain_canonical"]
                    ),
                    "repaired_full_domain_feasible_pool_ids": packet_payload["repaired_full_domain_feasible_pool_ids"],
                    "repaired_full_domain_candidate_count": packet_payload["repaired_full_domain_candidate_count"],
                    "repaired_full_domain_canonical_quote": packet_payload["repaired_full_domain_canonical_quote"],
                    "effective_quote_matches_full_domain_canonical": packet_payload[
                        "effective_quote_matches_full_domain_canonical"
                    ],
                    "repaired_key_cover_packet_ok": bool(packet_payload["repaired_key_cover_packet_ok"]),
                    "repaired_selected_keys_subset_full_keys": bool(
                        packet_payload["repaired_selected_keys_subset_full_keys"]
                    ),
                    "repaired_key_cover_holds": bool(packet_payload["repaired_key_cover_holds"]),
                    "repaired_selected_domain_canonical_matches_full_domain_canonical": bool(
                        packet_payload["repaired_selected_domain_canonical_matches_full_domain_canonical"]
                    ),
                    "repaired_key_cover_witness_count": int(packet_payload["repaired_key_cover_witness_count"]),
                    "repaired_key_cover_interpretation_packet_ok": bool(
                        packet_payload["repaired_key_cover_interpretation_packet_ok"]
                    ),
                    "repaired_key_cover_selected_winner_index_in_range": bool(
                        packet_payload["repaired_key_cover_selected_winner_index_in_range"]
                    ),
                    "repaired_key_cover_selected_winner_matches_certificate": bool(
                        packet_payload["repaired_key_cover_selected_winner_matches_certificate"]
                    ),
                    "repaired_key_cover_selected_winner_key_minimal": bool(
                        packet_payload["repaired_key_cover_selected_winner_key_minimal"]
                    ),
                    "repaired_key_cover_witness_indices_in_range": bool(
                        packet_payload["repaired_key_cover_witness_indices_in_range"]
                    ),
                    "repaired_key_cover_witness_coverage_complete": bool(
                        packet_payload["repaired_key_cover_witness_coverage_complete"]
                    ),
                    "repaired_key_cover_witness_keys_match_candidates": bool(
                        packet_payload["repaired_key_cover_witness_keys_match_candidates"]
                    ),
                    "repaired_key_cover_witness_domination_holds": bool(
                        packet_payload["repaired_key_cover_witness_domination_holds"]
                    ),
                    "effective_quote": packet_payload["effective_quote"],
                    "selected_runtime_quotes_agree": bool(packet.selected_runtime_quotes_agree),
                    "selected_domain_runtime_projected_path": packet_payload["selected_domain_runtime_projected_path"],
                    "advisory_projected_path": packet_payload["advisory_projected_path"],
                    "selected_domain_projection_cover_available": packet_payload["selected_domain_projection_cover_available"],
                    "selected_domain_projection_cover_holds": packet_payload["selected_domain_projection_cover_holds"],
                    "selected_domain_canonical_projected_path": packet_payload["selected_domain_canonical_projected_path"],
                    "selected_runtime_matches_selected_canonical_projected_path": packet_payload[
                        "selected_runtime_matches_selected_canonical_projected_path"
                    ],
                    "repaired_projection_cover_available": packet_payload["repaired_projection_cover_available"],
                    "repaired_projection_cover_holds": packet_payload["repaired_projection_cover_holds"],
                    "repaired_canonical_projected_path": packet_payload["repaired_canonical_projected_path"],
                    "advisory_matches_repaired_canonical_projected_path": packet_payload[
                        "advisory_matches_repaired_canonical_projected_path"
                    ],
                    "effective_projection_cover_side": packet_payload["effective_projection_cover_side"],
                    "effective_projection_cover_holds": packet_payload["effective_projection_cover_holds"],
                    "effective_canonical_projected_path": packet_payload["effective_canonical_projected_path"],
                    "effective_quote_projected_path": packet_payload["effective_quote_projected_path"],
                    "effective_quote_matches_canonical_projected_path": packet_payload[
                        "effective_quote_matches_canonical_projected_path"
                    ],
                }
                if quote is not None:
                    payload["quote"] = packet_payload["effective_quote"]
                else:
                    payload["error"] = str(err or "many_pool_certified_advisory_unavailable")
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "quote_exact_out_many_pool_certified_advisory_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    build_exact_out_many_pool_repaired_advisory_quote_packet,
                )

                packet = build_exact_out_many_pool_repaired_advisory_quote_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                response = {
                    "ok": True,
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
                }
                if not packet.packet_ok:
                    response["ok"] = False
                    response["error"] = str(packet.error or "many_pool_repaired_prefilter_contract_not_ok")
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_repaired_advisory_quote_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
                    build_exact_out_many_pool_repaired_full_domain_certified_packet,
                )

                packet = build_exact_out_many_pool_repaired_full_domain_certified_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                response = {
                    "ok": bool(packet.packet_ok),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
                    "quote_policy": "repaired_full_domain_certified_v1",
                }
                if not packet.packet_ok:
                    response["error"] = str(packet.error or "many_pool_repaired_advisory_not_full_domain_canonical")
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_repaired_full_domain_certified_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_repaired_key_cover_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA,
                    build_exact_out_many_pool_repaired_key_cover_packet,
                )

                packet = build_exact_out_many_pool_repaired_key_cover_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                response = {
                    "ok": bool(packet.packet_ok),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet",
                    "quote_policy": "repaired_key_cover_v1",
                }
                if not packet.packet_ok:
                    response["error"] = str(packet.error or "many_pool_repaired_selected_domain_not_key_cover_complete")
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_repaired_key_cover_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_repaired_key_cover_interpretation_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA,
                    build_exact_out_many_pool_repaired_key_cover_interpretation_packet,
                )

                packet = build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                response = {
                    "ok": bool(packet.packet_ok),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet",
                    "quote_policy": "repaired_key_cover_interpretation_v1",
                }
                if not packet.packet_ok:
                    response["error"] = str(
                        packet.error or "many_pool_repaired_key_cover_witness_interpretation_inconsistent"
                    )
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_repaired_key_cover_interpretation_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    build_exact_out_many_pool_bounded_advisory_quote_packet,
                )

                packet = build_exact_out_many_pool_bounded_advisory_quote_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                response = {
                    "ok": bool(packet.packet_ok),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
                }
                if not packet.packet_ok:
                    response["error"] = str(packet.error or "many_pool_bounded_advisory_unavailable")
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_bounded_advisory_quote_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_certified_advisory_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA,
                    build_exact_out_many_pool_certified_advisory_packet,
                )

                packet = build_exact_out_many_pool_certified_advisory_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                response = {
                    "ok": bool(packet.packet_ok),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
                }
                if not packet.packet_ok:
                    response["error"] = "many_pool_certified_advisory_packet_not_ok"
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_certified_advisory_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_repaired_replacement_shadow_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA,
                    build_exact_out_many_pool_repaired_replacement_shadow_packet,
                )

                packet = build_exact_out_many_pool_repaired_replacement_shadow_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": bool(packet.packet_ok),
                        "packet": packet.to_dict(),
                        "packet_schema": EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA,
                        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_repaired_replacement_shadow_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_default_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA,
                    build_exact_out_many_pool_default_packet,
                )

                packet = build_exact_out_many_pool_default_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                response = {
                    "ok": bool(packet.packet_ok),
                    "packet": packet.to_dict(),
                    "packet_schema": EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_default_packet",
                    "quote_policy": "certified_advisory_v1",
                }
                if not packet.packet_ok:
                    response["error"] = "many_pool_default_packet_not_ok"
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_default_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_bounded_workaround_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA,
                    build_exact_out_many_pool_bounded_workaround_packet,
                )

                packet = build_exact_out_many_pool_bounded_workaround_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "packet": packet.to_dict(),
                        "packet_schema": EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA,
                        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_bounded_workaround_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_oracle_contract":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                    build_exact_out_many_pool_oracle_contract,
                )

                contract = build_exact_out_many_pool_oracle_contract(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                contract_dict = contract.to_dict()
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "contract": contract_dict,
                        "contract_ok": bool(contract_dict["contract_ok"]),
                        "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_exact_out_many_pool_oracle_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_audited_bounds_contract":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA,
                    build_exact_out_many_pool_audited_bounds_contract,
                )

                contract = build_exact_out_many_pool_audited_bounds_contract(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "contract": contract.to_dict(),
                        "contract_schema": EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA,
                        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_audited_bounds_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA,
                    build_exact_out_many_pool_adaptive_liveness_packet,
                )

                packet = build_exact_out_many_pool_adaptive_liveness_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": bool(packet.packet_ok),
                        "packet": packet.to_dict(),
                        "packet_schema": EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA,
                        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
                        "quote_policy": "adaptive_liveness_v1",
                        "liveness_ok": bool(packet.liveness_ok),
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "build_exact_out_many_pool_adaptive_liveness_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/guard_exact_out_many_pool_canonicality":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                    guard_exact_out_many_pool_runtime_canonicality,
                )

                ok, err, contract = guard_exact_out_many_pool_runtime_canonicality(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                contract_dict = contract.to_dict()
                audit_payload = contract_dict["audit"]
                payload = {
                    "ok": bool(ok),
                    "contract": contract_dict,
                    "contract_ok": bool(contract_dict["contract_ok"]),
                    "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                    "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
                    "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
                    "runtime_projected_path": audit_payload["runtime_projected_path"],
                    "canonical_winner_projected_path": audit_payload["canonical_winner_projected_path"],
                    "runtime_matches_canonical_projected_path": audit_payload["runtime_matches_canonical_projected_path"],
                    "projection_cover_available": audit_payload["projection_cover_available"],
                    "projection_cover_holds": audit_payload["projection_cover_holds"],
                }
                if ok:
                    payload["quote"] = dict(contract_dict["audit"]["runtime_quote"])
                else:
                    payload["error"] = str(err or "many_pool_runtime_not_canonical")
                    payload["runtime_quote"] = dict(contract_dict["audit"]["runtime_quote"])
                    payload["canonical_winner_quote"] = dict(contract_dict["audit"]["canonical_winner_quote"])
                self._write_json(200, payload, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "guard_exact_out_many_pool_canonicality_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/quote_exact_out_many_pool_guarded":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True
                bridge_err = _check_routing_exact_out_oracle_adapter_bridge(
                    body=obj,
                    path=path,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                if bridge_err is not None:
                    self._write_json(
                        400,
                        {"ok": False, "error": "rejected", "detail": bridge_err},
                        cors_origin=cors_origin,
                    )
                    return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
                    EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                    quote_exact_out_many_pool_guarded,
                )

                quote, err, contract = quote_exact_out_many_pool_guarded(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                contract_dict = contract.to_dict()
                audit_payload = contract_dict["audit"]
                if quote is not None:
                    self._write_json(
                        200,
                        {
                            "ok": True,
                            "quote": dict(contract_dict["audit"]["runtime_quote"]),
                            "contract": contract_dict,
                            "contract_ok": bool(contract_dict["contract_ok"]),
                            "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                            "packet_schema": EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
                            "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
                            "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
                            "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
                            "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
                            "runtime_projected_path": audit_payload["runtime_projected_path"],
                            "canonical_winner_projected_path": audit_payload["canonical_winner_projected_path"],
                            "runtime_matches_canonical_projected_path": audit_payload[
                                "runtime_matches_canonical_projected_path"
                            ],
                            "projection_cover_available": audit_payload["projection_cover_available"],
                            "projection_cover_holds": audit_payload["projection_cover_holds"],
                        },
                        cors_origin=cors_origin,
                    )
                else:
                    self._write_json(
                        200,
                        {
                            "ok": False,
                            "error": str(err or "many_pool_runtime_not_canonical"),
                            "runtime_quote": dict(contract_dict["audit"]["runtime_quote"]),
                            "canonical_winner_quote": dict(contract_dict["audit"]["canonical_winner_quote"]),
                            "contract": contract_dict,
                            "contract_ok": bool(contract_dict["contract_ok"]),
                            "contract_schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
                            "packet_schema": EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
                            "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_oracle_contract",
                            "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_oracle_contract",
                            "build_packet_endpoint": "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
                            "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
                            "runtime_projected_path": audit_payload["runtime_projected_path"],
                            "canonical_winner_projected_path": audit_payload["canonical_winner_projected_path"],
                            "runtime_matches_canonical_projected_path": audit_payload[
                                "runtime_matches_canonical_projected_path"
                            ],
                            "projection_cover_available": audit_payload["projection_cover_available"],
                            "projection_cover_holds": audit_payload["projection_cover_holds"],
                        },
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "quote_exact_out_many_pool_guarded_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_guarded_quote_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True

                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
                    build_exact_out_many_pool_guarded_quote_packet,
                )

                packet = build_exact_out_many_pool_guarded_quote_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                packet_dict = packet.to_dict()
                response = {
                    "ok": True,
                    "packet": packet_dict,
                    "packet_schema": EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
                    "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
                }
                if not packet.guard_ok:
                    response["guard_ok"] = False
                    response["error"] = str(packet.error or "many_pool_runtime_not_canonical")
                self._write_json(200, response, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_exact_out_many_pool_guarded_quote_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_guarded_quote_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_guarded_quote_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_guarded_quote_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(200, {"ok": False, "error": err or "guarded quote packet verification failed"}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_exact_out_many_pool_guarded_quote_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/build_exact_out_many_pool_certified_winner_packet":
            try:
                pools_by_id = _parse_pools()
                asset_in = str(obj.get("asset_in", "")).strip()
                asset_out = str(obj.get("asset_out", "")).strip()
                amount_out_total = obj.get("amount_out_total")
                max_legs = obj.get("max_legs", 3)
                max_candidate_pools = obj.get("max_candidate_pools", 5)
                max_candidates = obj.get("max_candidates", 12)
                max_iters = obj.get("max_iters", 4096)
                window = obj.get("window", 64)
                brute_force_max = obj.get("brute_force_max", 512)
                max_full_domain_pools = obj.get("max_full_domain_pools", 8)
                max_enumerated_candidates = obj.get("max_enumerated_candidates", 20_000)
                if not asset_in or not asset_out or asset_in == asset_out:
                    self._write_json(400, {"ok": False, "error": "bad_assets"}, cors_origin=cors_origin)
                    return True
                int_fields = (
                    ("amount_out_total", amount_out_total, 1),
                    ("max_legs", max_legs, 1),
                    ("max_candidate_pools", max_candidate_pools, 1),
                    ("max_candidates", max_candidates, 1),
                    ("max_iters", max_iters, 1),
                    ("window", window, 0),
                    ("brute_force_max", brute_force_max, 0),
                    ("max_full_domain_pools", max_full_domain_pools, 1),
                    ("max_enumerated_candidates", max_enumerated_candidates, 1),
                )
                for field_name, value, min_value in int_fields:
                    if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                        self._write_json(400, {"ok": False, "error": f"bad_{field_name}"}, cors_origin=cors_origin)
                        return True
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA,
                    build_exact_out_many_pool_certified_winner_packet,
                )

                packet = build_exact_out_many_pool_certified_winner_packet(
                    list(pools_by_id.values()),
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_candidates=int(max_candidates),
                    max_iters=int(max_iters),
                    window=int(window),
                    brute_force_max=int(brute_force_max),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "packet": packet.to_dict(),
                        "packet_schema": EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA,
                        "verify_packet_endpoint": "/api/dex/verify_exact_out_many_pool_certified_winner_packet",
                    },
                    cors_origin=cors_origin,
                )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "build_exact_out_many_pool_certified_winner_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_certified_winner_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_certified_winner_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_certified_winner_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(200, {"ok": False, "error": err or "certified winner packet verification failed"}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_exact_out_many_pool_certified_winner_packet_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_repaired_advisory_quote_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_repaired_advisory_quote_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "repaired advisory quote packet verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_repaired_advisory_quote_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True, "quote_policy": "repaired_full_domain_certified_v1"}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {
                            "ok": False,
                            "error": err or "repaired full-domain certified packet verification failed",
                            "quote_policy": "repaired_full_domain_certified_v1",
                        },
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_repaired_full_domain_certified_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_repaired_key_cover_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_repaired_key_cover_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True, "quote_policy": "repaired_key_cover_v1"}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "repaired key-cover packet verification failed", "quote_policy": "repaired_key_cover_v1"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_repaired_key_cover_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload(packet)
                if ok:
                    self._write_json(
                        200,
                        {"ok": True, "quote_policy": "repaired_key_cover_interpretation_v1"},
                        cors_origin=cors_origin,
                    )
                else:
                    self._write_json(
                        200,
                        {
                            "ok": False,
                            "error": err or "repaired key-cover interpretation packet verification failed",
                            "quote_policy": "repaired_key_cover_interpretation_v1",
                        },
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_certified_advisory_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_certified_advisory_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_certified_advisory_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "certified advisory packet verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_certified_advisory_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "repaired replacement shadow packet verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_repaired_replacement_shadow_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_default_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_default_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_default_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True, "quote_policy": "certified_advisory_v1"}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "default packet verification failed", "quote_policy": "certified_advisory_v1"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_default_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_bounded_advisory_quote_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_bounded_advisory_quote_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "bounded advisory quote packet verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_bounded_advisory_quote_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_bounded_workaround_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_bounded_workaround_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "bounded workaround packet verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_bounded_workaround_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract":
            contract = obj.get("contract")
            if not isinstance(contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload,
                )

                ok, err = verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload(contract)
                if ok:
                    self._write_json(200, {"ok": True, "quote_policy": "repaired_selected_domain_v1"}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {
                            "ok": False,
                            "error": err or "repaired selected-domain oracle contract verification failed",
                            "quote_policy": "repaired_selected_domain_v1",
                        },
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_candidate_domain_contract":
            contract = obj.get("contract")
            if not isinstance(contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_candidate_domain_contract_payload,
                )

                ok, err = verify_exact_out_many_pool_candidate_domain_contract_payload(contract)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "candidate domain contract verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_candidate_domain_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_prefilter_contract":
            contract = obj.get("contract")
            if not isinstance(contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_prefilter_contract_payload,
                )

                ok, err = verify_exact_out_many_pool_prefilter_contract_payload(contract)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "prefilter contract verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_prefilter_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract":
            contract = obj.get("contract")
            if not isinstance(contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_repaired_prefilter_contract_payload,
                )

                ok, err = verify_exact_out_many_pool_repaired_prefilter_contract_payload(contract)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "repaired prefilter contract verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_repaired_prefilter_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_oracle_contract":
            contract = obj.get("contract")
            if not isinstance(contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_oracle_contract_payload,
                )

                ok, err = verify_exact_out_many_pool_oracle_contract_payload(contract)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(200, {"ok": False, "error": err or "oracle contract verification failed"}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_exact_out_many_pool_oracle_contract_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_audited_bounds_contract":
            contract = obj.get("contract")
            if not isinstance(contract, dict):
                self._write_json(400, {"ok": False, "error": "bad_contract"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_audited_bounds_contract_payload,
                )

                ok, err = verify_exact_out_many_pool_audited_bounds_contract_payload(contract)
                if ok:
                    self._write_json(200, {"ok": True}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {"ok": False, "error": err or "audited bounds contract verification failed"},
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_audited_bounds_contract_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet":
            packet = obj.get("packet")
            if not isinstance(packet, dict):
                self._write_json(400, {"ok": False, "error": "bad_packet"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_many_pool_adaptive_liveness_packet_payload,
                )

                ok, err = verify_exact_out_many_pool_adaptive_liveness_packet_payload(packet)
                if ok:
                    self._write_json(200, {"ok": True, "quote_policy": "adaptive_liveness_v1"}, cors_origin=cors_origin)
                else:
                    self._write_json(
                        200,
                        {
                            "ok": False,
                            "error": err or "adaptive liveness packet verification failed",
                            "quote_policy": "adaptive_liveness_v1",
                        },
                        cors_origin=cors_origin,
                    )
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {
                        "ok": False,
                        "error": "verify_exact_out_many_pool_adaptive_liveness_packet_error",
                        "details": "request failed",
                    },
                    cors_origin=cors_origin,
                )
                return True

        if path == "/api/dex/verify_exact_out_route_certificate":
            certificate = obj.get("certificate")
            if not isinstance(certificate, dict):
                self._write_json(400, {"ok": False, "error": "bad_certificate"}, cors_origin=cors_origin)
                return True
            try:
                from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
                    verify_exact_out_route_canonical_certificate_payload,
                )

                ok, err = verify_exact_out_route_canonical_certificate_payload(certificate)
                self._write_json(200, {"ok": bool(ok), "error": ("ok" if ok else str(err))}, cors_origin=cors_origin)
                return True
            except Exception as exc:
                self._write_json(
                    400,
                    {"ok": False, "error": "verify_exact_out_certificate_error", "details": "request failed"},
                    cors_origin=cors_origin,
                )
                return True

        self._write_json(404, {"ok": False, "error": "not_found"}, cors_origin=cors_origin)
        return True

    def do_OPTIONS(self) -> None:  # noqa: N802
        cors_origin = self._allowed_cors_origin_or_none()
        if cors_origin is None:
            self.send_response(204)
            self.end_headers()
            return
        safe_cors_origin = _safe_cors_origin(cors_origin)
        if safe_cors_origin is None:
            self.send_response(204)
            self.end_headers()
            return
        self.send_response(204)
        if "\r" not in safe_cors_origin and "\n" not in safe_cors_origin:
            self.send_header("Access-Control-Allow-Origin", safe_cors_origin)
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
        if self._maybe_handle_autogov_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_zusd_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_autotrader_live_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_confidential_attestation_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_confidential_sealed_bid_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return

        self._write_json(404, {"ok": False, "error": "not_found"}, cors_origin=cors_origin)

    def do_POST(self) -> None:  # noqa: N802
        cors_origin = self._allowed_cors_origin_or_none()
        if not self._maybe_rate_limit():
            self._write_json(429, {"ok": False, "error": "rate_limited"}, cors_origin=cors_origin)
            return

        path = (self.path or "").split("?", 1)[0]

        raw_body = None
        if (
            path.startswith("/api/perps/")
            or path.startswith("/api/zusd/")
            or path.startswith("/api/dex/")
            or path.startswith("/api/autogov/")
            or path.startswith("/api/strategy/autotrader/")
            or path.startswith("/api/confidential/attestation/")
            or path.startswith("/api/confidential/sealed-bid/")
        ):
            ctype = (self.headers.get("Content-Type") or "").split(";", 1)[0].strip().lower()
            if ctype and ctype != "application/json":
                self._write_json(415, {"ok": False, "error": "unsupported_media_type"}, cors_origin=cors_origin)
                return
            raw_body, err = self._read_raw_body_with_error(max_bytes=self._max_post_body_bytes_for_path(path))
            if err is not None:
                status, code = err
                self._write_json(int(status), {"ok": False, "error": str(code)}, cors_origin=cors_origin)
                return
        if self._maybe_handle_perps_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_autogov_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_zusd_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_autotrader_live_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_confidential_attestation_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_confidential_sealed_bid_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_dex_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return

        self._write_json(404, {"ok": False, "error": "not_found"}, cors_origin=cors_origin)

    def log_message(self, fmt: str, *args: object) -> None:
        # BaseHTTPRequestHandler's default message can include the full request
        # line. Avoid formatting request-derived values into clear-text logs.
        _ = (fmt, args)
        print("zenodex-api request event")

    def log_request(self, code: int | str = "-", size: int | str = "-") -> None:
        # Keep access logs useful without recording paths, queries, or headers.
        safe_code = str(code) if str(code).isdigit() else "-"
        safe_size = str(size) if str(size).isdigit() else "-"
        print(f"zenodex-api request status={safe_code} size={safe_size}")


def _api_bearer_token_from_env() -> str:
    """Return the configured direct API bearer token.

    ``DEMO_API_TOKEN`` is kept as a legacy local/dev alias. Prefer
    ``ZENODEX_API_BEARER_TOKEN`` because the Docker/nginx local-testnet stack
    and UI runtime config use that name.
    """

    return _env_str("ZENODEX_API_BEARER_TOKEN", "") or _env_str("DEMO_API_TOKEN", "")


def _legacy_demo_auth_only_from_env() -> bool:
    return _env_str("DEMO_API_TOKEN", "") != "" and _env_str("ZENODEX_API_BEARER_TOKEN", "") == ""


def _demo_auth_configured_from_env() -> bool:
    return _api_bearer_token_from_env() != ""


def _api_auth_posture_error_code(
    *,
    protected_api_enabled: bool,
    external_auth_enforced: bool,
    production_mode: bool,
    allow_demo_auth: bool,
    loopback_host: bool,
) -> str | None:
    api_bearer_token_configured = _demo_auth_configured_from_env()
    legacy_demo_auth_only = _legacy_demo_auth_only_from_env()
    if protected_api_enabled and not external_auth_enforced and not api_bearer_token_configured:
        return "missing_auth"
    if (
        protected_api_enabled
        and not external_auth_enforced
        and legacy_demo_auth_only
        and production_mode
        and not allow_demo_auth
    ):
        return "demo_auth_in_production"
    if (
        protected_api_enabled
        and not external_auth_enforced
        and legacy_demo_auth_only
        and not loopback_host
        and not allow_demo_auth
    ):
        return "demo_auth_non_loopback"
    return None


def _print_api_auth_posture_error(code: str) -> None:
    messages = {
        "missing_auth": (
            "Refusing to start: protected APIs enabled without external auth or "
            "ZENODEX_API_BEARER_TOKEN."
        ),
        "demo_auth_in_production": (
            "Refusing to start: the configured demo credential is demo/dev auth only. "
            "Set ZENODEX_EXTERNAL_AUTH_ENFORCED=1 for a real auth gateway, or "
            "ALLOW_DEMO_TOKEN_AUTH=1 only for a controlled demo."
        ),
        "demo_auth_non_loopback": (
            "Refusing to start: demo auth on a non-loopback bind requires "
            "ALLOW_DEMO_TOKEN_AUTH=1 for an explicitly scoped demo."
        ),
    }
    line = messages.get(code, "Refusing to start: API auth posture is invalid.")
    os.write(1, (line + "\n").encode("utf-8"))


def main(argv: Optional[Sequence[str]] = None) -> int:
    _ = argv
    from src.runtime.authority import reset_active_authority_policy  # pylint: disable=import-outside-toplevel

    reset_active_authority_policy()
    host = _env_str("API_HOST", "127.0.0.1")
    try:
        port = _env_int("API_PORT", 8000, lo=1, hi=65535)
        rpm = _env_int("RATE_LIMIT_RPM", 600, lo=0, hi=1_000_000)
        max_buckets = _env_int("RATE_LIMIT_MAX_BUCKETS", 10_000, lo=1, hi=1_000_000)
    except ValueError as exc:
        print(f"Refusing to start: invalid integer environment variable: {exc}")
        return 2
    cors_origins = _parse_cors_origins(_env_str("CORS_ORIGINS", ""))

    try:
        perps_enabled = _env_bool("PERPS_API_ENABLED", False)
        perps_wallet_enabled = _env_bool("PERPS_WALLET_API_ENABLED", False)
        zusd_enabled = _env_bool("ZUSD_API_ENABLED", False)
        zusd_tau_wallet_enabled = _env_bool("ZUSD_TAU_WALLET_API_ENABLED", False)
        zusd_monetary_wallet_enabled = _env_bool("ZUSD_MONETARY_WALLET_API_ENABLED", False)
        autotrader_live_enabled = _env_bool("AUTOTRADER_LIVE_API_ENABLED", False)
        autogov_live_apply_enabled = _env_bool("AUTOGOV_LIVE_APPLY_API_ENABLED", False)
        confidential_attestation_enabled = _env_bool(
            "CONFIDENTIAL_ATTESTATION_API_ENABLED", False
        )
        confidential_sealed_bid_feature_enabled = _env_bool("CONFIDENTIAL_SEALED_BID_ENABLED", True)
        confidential_sealed_bid_enabled = _env_bool(
            "CONFIDENTIAL_SEALED_BID_API_ENABLED",
            confidential_attestation_enabled and confidential_sealed_bid_feature_enabled,
        )
        dex_enabled = _env_bool("DEX_API_ENABLED", False)
        external_auth_enforced = _env_bool("ZENODEX_EXTERNAL_AUTH_ENFORCED", False)
        allow_demo_token_auth = _env_bool("ALLOW_DEMO_TOKEN_AUTH", False)
        _routing_oracle_adapter_required = _env_bool(
            "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", False
        )
    except ValueError as exc:
        print(f"Refusing to start: invalid boolean environment variable: {exc}")
        return 2
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env  # pylint: disable=import-outside-toplevel
    confidential_feature_status = load_confidential_feature_status_from_env().to_public_dict()
    from src.state.confidential_requests import ConfidentialRequestTable  # pylint: disable=import-outside-toplevel

    sensitive_api_enabled = bool(
        perps_enabled
        or perps_wallet_enabled
        or zusd_enabled
        or zusd_tau_wallet_enabled
        or zusd_monetary_wallet_enabled
        or autotrader_live_enabled
        or autogov_live_apply_enabled
        or confidential_attestation_enabled
        or confidential_sealed_bid_enabled
        or dex_enabled
    )
    runtime_env = _env_str("ZENODEX_ENV", _env_str("APP_ENV", "production")).lower()
    production_mode = runtime_env not in ("dev", "development", "test", "local")
    auth_error_code = _api_auth_posture_error_code(
        protected_api_enabled=sensitive_api_enabled,
        external_auth_enforced=external_auth_enforced,
        production_mode=production_mode,
        allow_demo_auth=allow_demo_token_auth,
        loopback_host=_is_loopback_host(host),
    )
    if auth_error_code is not None:
        _print_api_auth_posture_error(auth_error_code)
        return 2

    _deploy_profile_id = _env_str("ZENODEX_DEPLOY_PROFILE", "").strip()
    if _deploy_profile_id:
        from src.integration.deploy_profile import (  # pylint: disable=import-outside-toplevel
            evaluate_deploy_profile_consistency,
            load_deploy_profile,
        )

        try:
            _deploy_profile = load_deploy_profile(_deploy_profile_id)
            _deploy_conflicts = evaluate_deploy_profile_consistency(
                _deploy_profile,
                {
                    "sensitive_api_enabled": sensitive_api_enabled,
                    "external_auth_enforced": external_auth_enforced,
                    "auth_bearer_token_set": _api_bearer_token_from_env() != "",
                    "allow_demo_token_auth": allow_demo_token_auth,
                    "legacy_demo_token_active": _env_str("DEMO_API_TOKEN", "") != "",
                    "confidential_sealed_bid_allow_in_memory_state": _env_bool(
                        "CONFIDENTIAL_SEALED_BID_ALLOW_IN_MEMORY_STATE", False
                    ),
                    "confidential_sealed_bid_allow_fixture_settlement": _env_bool(
                        "CONFIDENTIAL_SEALED_BID_ALLOW_FIXTURE_SETTLEMENT", False
                    ),
                    "confidential_sealed_bid_return_signed_tau_tx_payload": _env_bool(
                        "CONFIDENTIAL_SEALED_BID_RETURN_SIGNED_TAU_TX_PAYLOAD", False
                    ),
                    "perps_wallet_allow_local_signing": _env_bool("PERPS_WALLET_ALLOW_LOCAL_SIGNING", False),
                    "perps_wallet_return_signed_tau_tx_payload": _env_bool(
                        "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD", False
                    ),
                    "zusd_tau_wallet_allow_local_signing": _env_bool(
                        "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", False
                    ),
                    "zusd_tau_wallet_return_signed_tau_tx_payload": _env_bool(
                        "ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD", False
                    ),
                    "zusd_monetary_wallet_allow_local_signing": _env_bool(
                        "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING",
                        _env_bool("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", False),
                    ),
                    "autotrader_live_allow_local_signing": _env_bool(
                        "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", False
                    ),
                    "dex_routing_oracle_adapter_required": _env_bool(
                        "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED", False
                    ),
                    "zusd_oracle_adapter_required": _env_bool("ZUSD_ORACLE_ADAPTER_REQUIRED", False),
                    "zusd_oracle_authorization_required": _env_bool(
                        "ZUSD_ORACLE_AUTHORIZATION_REQUIRED", False
                    ),
                    "zusd_monetary_wallet_oracle_authorization_required": _env_bool(
                        "ZUSD_MONETARY_WALLET_ORACLE_AUTHORIZATION_REQUIRED",
                        _env_bool("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", False),
                    ),
                    "perps_clearinghouse_settle_oracle_adapter_required": _env_bool(
                        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH", False
                    ),
                    "perps_clearinghouse_settle_oracle_authorization_required": _env_bool(
                        "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH", False
                    ),
                    "perps_isolated_settle_oracle_adapter_required": _env_bool(
                        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_SETTLE_EPOCH", False
                    ),
                    "perps_isolated_partial_liquidate_oracle_adapter_required": _env_bool(
                        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE", False
                    ),
                    "perps_isolated_settle_oracle_authorization_required": _env_bool(
                        "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_ISOLATED_SETTLE_EPOCH", False
                    ),
                    "enabled_routes": tuple(
                        route
                        for route, enabled in (
                            ("local_demo", bool(perps_enabled or perps_wallet_enabled)),
                            (
                                "local_demo",
                                bool(zusd_enabled or zusd_tau_wallet_enabled or zusd_monetary_wallet_enabled),
                            ),
                            ("local_demo", bool(autotrader_live_enabled)),
                            ("local_demo", bool(confidential_attestation_enabled or confidential_sealed_bid_enabled)),
                            ("local_demo", bool(dex_enabled)),
                        )
                        if enabled
                    ),
                },
            )
        except (OSError, ValueError, TypeError) as exc:
            print(f"Refusing to start: invalid ZENODEX_DEPLOY_PROFILE={_deploy_profile_id!r}: {exc}")
            return 2
        if _deploy_conflicts:
            for _conflict in _deploy_conflicts:
                print(f"Refusing to start: {_conflict}")
            return 2

        from src.runtime.authority import (  # pylint: disable=import-outside-toplevel
            AuthorityError,
            RUST_AUTHORITATIVE_MODES,
            RustUnavailable,
            load_authority_policy,
            set_active_authority_policy,
            validate_authority_policy,
        )

        try:
            _authority_policy = load_authority_policy(_deploy_profile)
            validate_authority_policy(_authority_policy, profile_id=_deploy_profile_id)
        except (AuthorityError, ValueError, TypeError) as exc:
            print(
                f"Refusing to start: invalid runtime_authority_policy in "
                f"{_deploy_profile_id!r}: {exc}"
            )
            return 2
        if (
            _authority_policy.default in RUST_AUTHORITATIVE_MODES
            or any(mode in RUST_AUTHORITATIVE_MODES for mode in _authority_policy.per_surface.values())
        ):
            from src.runtime.rust_invoker import locate_runtime_binary  # pylint: disable=import-outside-toplevel

            try:
                locate_runtime_binary()
            except RustUnavailable as exc:
                _rust_error = (
                    "Refusing to start: runtime_authority_policy in "
                    f"{_deploy_profile_id!r} requires Rust authority but "
                    f"zenodex-runtime is unavailable: {exc}"
                )
                print(
                    _rust_error
                )
                return 2
        set_active_authority_policy(_authority_policy)

    # API-surface profile gate (D-CONFIG-002): the profiles in
    # api_surface_profiles.py (e.g. production-strict forbids demo/value-moving
    # routes) were defined but never enforced at startup, so a production-strict
    # deployment could still serve perps/zUSD/DEX writer routes. Enforce the
    # selected profile against the active runtime flags. Opt-in via
    # ZENODEX_API_SURFACE_PROFILE (or the existing API_SURFACE_PROFILE alias);
    # fail-closed on any violation, unknown id, or inconsistent aliases.
    _api_surface_profile_id = _env_str("ZENODEX_API_SURFACE_PROFILE", "").strip()
    _api_surface_profile_alias = _env_str("API_SURFACE_PROFILE", "").strip()
    if (
        _api_surface_profile_id
        and _api_surface_profile_alias
        and _api_surface_profile_id != _api_surface_profile_alias
    ):
        print(
            "Refusing to start: inconsistent API surface profiles "
            f"ZENODEX_API_SURFACE_PROFILE={_api_surface_profile_id!r} "
            f"API_SURFACE_PROFILE={_api_surface_profile_alias!r}"
        )
        return 2
    _api_surface_profile_id = _api_surface_profile_id or _api_surface_profile_alias
    if _api_surface_profile_id:
        from src.integration.api_surface_profiles import (  # pylint: disable=import-outside-toplevel
            api_surface_profile_violations,
        )

        try:
            _surface_violations = api_surface_profile_violations(
                profile_id=_api_surface_profile_id,
                demo_api_token=_api_bearer_token_from_env(),
                perps_enabled=bool(perps_enabled or perps_wallet_enabled or autotrader_live_enabled),
                zusd_enabled=bool(
                    zusd_enabled or zusd_tau_wallet_enabled or zusd_monetary_wallet_enabled
                ),
                dex_enabled=bool(dex_enabled),
                confidential_enabled=bool(confidential_attestation_enabled or confidential_sealed_bid_enabled),
            )
        except ValueError as exc:
            print(
                f"Refusing to start: invalid ZENODEX_API_SURFACE_PROFILE="
                f"{_api_surface_profile_id!r}: {exc}"
            )
            return 2
        if _surface_violations:
            for _violation in _surface_violations:
                print(f"Refusing to start: {_violation}")
            return 2

    httpd = ThreadingHTTPServer((host, port), _Handler)
    # Attach config to server instance (used by handler).
    httpd.cors_origins = cors_origins  # type: ignore[attr-defined]
    httpd.rate_limiter = TokenBucketRateLimiter(rpm=rpm, max_buckets=max_buckets)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = perps_enabled  # type: ignore[attr-defined]
    httpd.perps_wallet_api_enabled = perps_wallet_enabled  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = zusd_enabled  # type: ignore[attr-defined]
    httpd.zusd_tau_wallet_api_enabled = zusd_tau_wallet_enabled  # type: ignore[attr-defined]
    httpd.zusd_monetary_wallet_api_enabled = zusd_monetary_wallet_enabled  # type: ignore[attr-defined]
    httpd.autogov_live_apply_api_enabled = autogov_live_apply_enabled  # type: ignore[attr-defined]
    httpd.autotrader_live_api_enabled = autotrader_live_enabled  # type: ignore[attr-defined]
    httpd.autotrader_execution_keys = set()  # type: ignore[attr-defined]
    httpd.autotrader_supervisor_runs = {}  # type: ignore[attr-defined]
    httpd.autotrader_execution_lock = threading.Lock()  # type: ignore[attr-defined]
    httpd.confidential_attestation_api_enabled = confidential_attestation_enabled  # type: ignore[attr-defined]
    httpd.confidential_sealed_bid_api_enabled = confidential_sealed_bid_enabled  # type: ignore[attr-defined]
    httpd.dex_api_enabled = dex_enabled  # type: ignore[attr-defined]
    httpd.confidential_feature_status = confidential_feature_status  # type: ignore[attr-defined]
    httpd.confidential_request_table = ConfidentialRequestTable()  # type: ignore[attr-defined]
    httpd.confidential_request_lock = threading.Lock()  # type: ignore[attr-defined]
    httpd.confidential_sealed_bid_state = {}  # type: ignore[attr-defined]
    httpd.confidential_sealed_bid_state_file = _env_str("CONFIDENTIAL_SEALED_BID_STATE_FILE", "")  # type: ignore[attr-defined]
    httpd.confidential_sealed_bid_lock = threading.Lock()  # type: ignore[attr-defined]

    startup_line = (
        f"zenodex-api listening on http://{host}:{port} "
        f"(cors_origins={sorted(cors_origins)}, rpm={rpm}, max_buckets={max_buckets}, "
        f"perps_api={perps_enabled}, perps_wallet_api={perps_wallet_enabled}, zusd_api={zusd_enabled}, "
        f"zusd_tau_wallet_api={zusd_tau_wallet_enabled}, "
        f"zusd_monetary_wallet_api={zusd_monetary_wallet_enabled}, "
        f"autotrader_live_api={autotrader_live_enabled}, "
        f"autogov_live_apply_api={autogov_live_apply_enabled}, "
        f"confidential_attestation_api={confidential_attestation_enabled}, "
        f"confidential_sealed_bid_api={confidential_sealed_bid_enabled}, dex_api={dex_enabled}, "
        f"confidential_stage={confidential_feature_status.get('stage')}, "
        f"external_auth_enforced={external_auth_enforced}, "
        f"demo_auth_allowed={allow_demo_token_auth})"
    )
    os.write(1, (startup_line + "\n").encode("utf-8"))
    httpd.demo_api_token = _api_bearer_token_from_env()  # type: ignore[attr-defined]
    httpd.serve_forever(poll_interval=0.25)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
