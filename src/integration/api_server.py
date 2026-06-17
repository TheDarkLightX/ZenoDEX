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
- Bearer-token auth for explicitly enabled local/testnet routes (ZENODEX_API_BEARER_TOKEN)
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
    except ImportError:
        pass


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        v = int(raw.strip())
    except ValueError:
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


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    return raw.strip().lower() in ("1", "true", "yes", "on")


def _confidential_sealed_bid_enabled_from_env() -> bool:
    """Resolve whether the confidential sealed-bid settlement API is enabled.

    The sealed-bid API is a *distinct* privileged writer surface: it admits and
    settles confidential asset trades against the local ledger. It must require
    its OWN explicit opt-in and must NOT be implied by enabling the separate
    confidential *attestation* API. Previously the default inherited
    ``CONFIDENTIAL_ATTESTATION_API_ENABLED``, so an operator who enabled only
    attestation silently turned on the sealed-bid writer surface as well
    (disaster class D-CONFIG-001: env default weakens production boundary).

    Fail-closed: every sensitive-API flag requires explicit ``1/true/yes/on``.
    """
    return _env_bool("CONFIDENTIAL_SEALED_BID_API_ENABLED", False)


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
    except ImportError as exc:
        return f"oracle_adapter_bridge verifier unavailable: {type(exc).__name__}"

    try:
        result = verify_aggregate_adapter_bridge(bridge)
    except (TypeError, ValueError) as exc:
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
        """Bearer-token check for sensitive local/testnet routes.

        Review note (grade A-): this handler used to allow requests whenever
        no token was attached, relying on startup validation to make that state
        unreachable. Sensitive routes should stay fail-closed at the request
        boundary too; only an explicit external-auth server flag may bypass the
        in-process bearer check.
        """
        token = getattr(self.server, "demo_api_token", "")  # type: ignore[attr-defined]
        if not isinstance(token, str) or not token:
            return bool(getattr(self.server, "external_auth_enforced", False))  # type: ignore[attr-defined]
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
        # No HTTP exposure for non-wallet /api/perps/* routes. The signed
        # production write path is /api/perps/wallet/submit. The in-memory
        # audit-replay scaffold lives at src/integration/_perps_audit_replay_state.py
        # and is imported only by tools/check_* audit harnesses, never served.
        return False

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

        status, resp = handle_perps_wallet_request(method, path, raw_body)
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
        # No HTTP exposure for non-wallet /api/zusd/* routes. Signed
        # production writes go through /api/zusd/wallet/* and
        # /api/zusd/monetary/*. The in-memory audit-replay scaffold lives
        # at src/integration/_zusd_audit_replay_state.py and is imported
        # only by tools/check_* audit harnesses, never served.
        return False

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

        status, resp = handle_zusd_tau_wallet_request(method, path, raw_body)
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

        status, resp = handle_zusd_monetary_wallet_request(method, path, raw_body)
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

        table = getattr(self.server, "confidential_sealed_bid_table", None)  # type: ignore[attr-defined]
        asset_settlement_submitter = getattr(  # type: ignore[attr-defined]
            self.server,
            "confidential_sealed_bid_asset_settlement_submitter",
            None,
        )
        lock = getattr(self.server, "confidential_sealed_bid_lock", None)  # type: ignore[attr-defined]
        if lock is not None:
            with lock:
                status, resp = handle_confidential_sealed_bid_request(
                    method,
                    path,
                    raw_body,
                    table=table,
                    asset_settlement_submitter=asset_settlement_submitter,
                )
        else:
            status, resp = handle_confidential_sealed_bid_request(
                method,
                path,
                raw_body,
                table=table,
                asset_settlement_submitter=asset_settlement_submitter,
            )
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
        # Step 7: serve the auto-generated OpenAPI 3.1 document. GET-only.
        # Only the schema-backed (Step 6) endpoints appear; ad-hoc-validated
        # handlers are intentionally omitted so the published surface
        # never lies about the contract.
        if path == "/api/dex/openapi.json" and method == "GET":
            from src.integration.api_server_dex_dispatch import (  # pylint: disable=import-outside-toplevel
                generate_openapi_document,
            )

            self._write_json(200, generate_openapi_document(), cors_origin=cors_origin)
            return True
        # Step 8: per-endpoint dispatch metrics (request count, error
        # count, latency p50/p95/p99). GET-only. Operator-facing.
        if path == "/api/dex/metrics" and method == "GET":
            from src.integration.api_server_dex_dispatch import (  # pylint: disable=import-outside-toplevel
                serve_metrics,
            )

            self._write_json(200, serve_metrics(), cors_origin=cors_origin)
            return True
        if method != "POST":
            self._write_json(405, {"ok": False, "error": "method_not_allowed"}, cors_origin=cors_origin)
            return True
        if raw_body is None:
            self._write_json(400, {"ok": False, "error": "missing_body"}, cors_origin=cors_origin)
            return True

        try:
            obj = json.loads(raw_body)
        except (json.JSONDecodeError, UnicodeDecodeError):
            self._write_json(400, {"ok": False, "error": "bad_json"}, cors_origin=cors_origin)
            return True
        if not isinstance(obj, dict):
            self._write_json(400, {"ok": False, "error": "bad_body"}, cors_origin=cors_origin)
            return True
        search_limit_error = _dex_api_search_limit_error(path, obj)
        if search_limit_error is not None:
            self._write_json(400, {"ok": False, "error": search_limit_error}, cors_origin=cors_origin)
            return True

        # Strangler-fig dispatch: handlers migrated to api_server_dex_dispatch
        # take precedence over the legacy if-chain below. New endpoints should
        # be added to dex_dispatch_handlers.py, not here. The dispatcher
        # absorbs DexEndpointError and applies the per-endpoint catch-all
        # error_code, so individual handlers don't need their own
        # try/except.
        from src.integration.api_server_dex_dispatch import (  # pylint: disable=import-outside-toplevel
            DexRequestContext as _DexRequestContext,
            dispatch as _dex_dispatch,
        )

        _ctx = _DexRequestContext(server=self.server, cors_origin=cors_origin, raw_body=raw_body)
        _dispatched = _dex_dispatch(path, obj, _ctx)
        if _dispatched is not None:
            _status, _body = _dispatched
            self._write_json(_status, _body, cors_origin=cors_origin)
            return True

        # Closures kept as thin wrappers around helpers in _dex_api_helpers
        # so the legacy if-chain below still calls them by their original
        # names. Migrated handlers in dex_dispatch_handlers.py import the
        # helpers directly.
        from src.integration._dex_api_helpers import (  # pylint: disable=import-outside-toplevel
            parse_pools as _parse_pools_helper,
            projected_path_from_exact_out_quote_payload as _projected_path_from_exact_out_quote_payload,
        )

        def _parse_pools() -> dict[str, Any]:
            return _parse_pools_helper(obj)
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
            self._write_json(200, {"ok": True, "status": "healthy", "service": "zenodex-api"}, cors_origin=cors_origin)
            return

        if path == "/version":
            self._write_json(
                200,
                {
                    "ok": True,
                    "service": "zenodex-api",
                    "python": os.environ.get("PYTHON_VERSION", ""),
                },
                cors_origin=cors_origin,
            )
            return

        if path == "/api/confidential/status":
            status = getattr(self.server, "confidential_feature_status", None)
            if not isinstance(status, dict):
                from src.integration.confidential_feature_status import (  # pylint: disable=import-outside-toplevel
                    load_confidential_feature_status_from_env,
                )

                status = load_confidential_feature_status_from_env().to_public_dict()
            self._write_json(200, {"ok": True, "status": status}, cors_origin=cors_origin)
            return

        if self._maybe_handle_perps_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_zusd_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_autogov_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_autotrader_live_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_confidential_attestation_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        if self._maybe_handle_confidential_sealed_bid_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
            return
        # Step 7: /api/dex/openapi.json (GET-only auto-generated spec).
        # The dex API handler is normally POST-only, but this single GET
        # route is required for introspection. Routed last so other GET
        # surfaces take precedence.
        if self._maybe_handle_dex_api(method="GET", path=path, cors_origin=cors_origin, raw_body=None):
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
            or path.startswith("/api/strategy/autotrader/")
            or path.startswith("/api/confidential/attestation/")
            or path.startswith("/api/confidential/sealed-bid/")
            or path.startswith("/api/autogov/")
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
        if self._maybe_handle_zusd_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
            return
        if self._maybe_handle_autogov_api(method="POST", path=path, cors_origin=cors_origin, raw_body=raw_body):
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


def main(argv: Optional[Sequence[str]] = None) -> int:
    _ = argv
    host = _env_str("API_HOST", "127.0.0.1")
    port = _env_int("API_PORT", 8000, lo=1, hi=65535)
    cors_origins = _parse_cors_origins(_env_str("CORS_ORIGINS", ""))
    rpm = _env_int("RATE_LIMIT_RPM", 600, lo=0, hi=1_000_000)
    max_buckets = _env_int("RATE_LIMIT_MAX_BUCKETS", 10_000, lo=1, hi=1_000_000)

    perps_wallet_enabled = _env_str("PERPS_WALLET_API_ENABLED", "false").lower() in ("1", "true", "yes")
    zusd_tau_wallet_enabled = _env_str("ZUSD_TAU_WALLET_API_ENABLED", "false").lower() in ("1", "true", "yes")
    zusd_monetary_wallet_enabled = _env_str("ZUSD_MONETARY_WALLET_API_ENABLED", "false").lower() in ("1", "true", "yes")
    autotrader_live_enabled = _env_str("AUTOTRADER_LIVE_API_ENABLED", "false").lower() in ("1", "true", "yes")
    confidential_attestation_enabled = _env_str("CONFIDENTIAL_ATTESTATION_API_ENABLED", "false").lower() in (
        "1",
        "true",
        "yes",
    )
    confidential_sealed_bid_enabled = _confidential_sealed_bid_enabled_from_env()
    confidential_sealed_bid_state_file = _env_str("CONFIDENTIAL_SEALED_BID_STATE_FILE", "")
    dex_enabled = _env_str("DEX_API_ENABLED", "false").lower() in ("1", "true", "yes")
    autogov_live_apply_enabled = _env_str("AUTOGOV_LIVE_APPLY_API_ENABLED", "false").lower() in (
        "1",
        "true",
        "yes",
    )
    api_bearer_token = _env_str("ZENODEX_API_BEARER_TOKEN", "")
    legacy_demo_api_token = _env_str("DEMO_API_TOKEN", "")
    auth_bearer_token = api_bearer_token or legacy_demo_api_token
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env  # pylint: disable=import-outside-toplevel
    confidential_feature_status = load_confidential_feature_status_from_env().to_public_dict()
    from src.integration.confidential_sealed_bid_api import (  # pylint: disable=import-outside-toplevel
        ConfidentialSealedBidTable,
        submit_confidential_sealed_bid_local_ledger_settlement,
    )
    from src.state.confidential_requests import ConfidentialRequestTable  # pylint: disable=import-outside-toplevel

    sensitive_api_enabled = bool(
        perps_wallet_enabled
        or zusd_tau_wallet_enabled
        or zusd_monetary_wallet_enabled
        or autotrader_live_enabled
        or confidential_attestation_enabled
        or confidential_sealed_bid_enabled
        or dex_enabled
        or autogov_live_apply_enabled
    )
    runtime_env = _env_str("ZENODEX_ENV", _env_str("APP_ENV", "production")).lower()
    production_mode = runtime_env not in ("dev", "development", "test", "local")
    external_auth_enforced = _env_bool("ZENODEX_EXTERNAL_AUTH_ENFORCED", False)
    allow_demo_token_auth = _env_bool("ALLOW_DEMO_TOKEN_AUTH", False)
    allow_in_memory_sealed_bid = _env_bool("CONFIDENTIAL_SEALED_BID_ALLOW_IN_MEMORY_STATE", False)

    legacy_demo_token_active = bool(legacy_demo_api_token and not api_bearer_token)

    if sensitive_api_enabled and not external_auth_enforced and not auth_bearer_token:
        print(
            "Refusing to start: sensitive APIs enabled without external auth or ZENODEX_API_BEARER_TOKEN "
            f"(host={host!r}, perps_wallet_api={perps_wallet_enabled}, "
            f"zusd_tau_wallet_api={zusd_tau_wallet_enabled}, "
            f"zusd_monetary_wallet_api={zusd_monetary_wallet_enabled}, "
            f"autotrader_live_api={autotrader_live_enabled}, "
            f"confidential_attestation_api={confidential_attestation_enabled}, "
            f"confidential_sealed_bid_api={confidential_sealed_bid_enabled}, "
            f"dex_api={dex_enabled}, autogov_live_apply_api={autogov_live_apply_enabled})"
        )
        return 2
    if confidential_sealed_bid_enabled and production_mode and not confidential_sealed_bid_state_file and not allow_in_memory_sealed_bid:
        print(
            "Refusing to start: confidential sealed-bid API requires "
            "CONFIDENTIAL_SEALED_BID_STATE_FILE in production mode. "
            "Set CONFIDENTIAL_SEALED_BID_ALLOW_IN_MEMORY_STATE=1 only for controlled demos."
        )
        return 2
    if sensitive_api_enabled and not external_auth_enforced and legacy_demo_token_active and production_mode and not allow_demo_token_auth:
        print(
            "Refusing to start: DEMO_API_TOKEN is demo/dev auth only. "
            "Set ZENODEX_EXTERNAL_AUTH_ENFORCED=1 for a real auth gateway, or "
            "ALLOW_DEMO_TOKEN_AUTH=1 only for a controlled demo."
        )
        return 2
    if (
        sensitive_api_enabled
        and not external_auth_enforced
        and legacy_demo_token_active
        and not _is_loopback_host(host)
        and not allow_demo_token_auth
    ):
        print(
            "Refusing to start: demo-token auth on a non-loopback bind requires "
            "ALLOW_DEMO_TOKEN_AUTH=1 for an explicitly scoped demo."
        )
        return 2

    # Deploy-profile consistency gate (D-CONFIG-002): when a deployment profile is
    # selected, the declared policy in config/deploy/<profile>.yaml is parsed and
    # enforced against the active runtime env. The profiles were previously
    # documentation-only; this makes them load-bearing. Fail-closed on conflict.
    deploy_profile_id = _env_str("ZENODEX_DEPLOY_PROFILE", "")
    if deploy_profile_id:
        from src.integration.deploy_profile import (  # pylint: disable=import-outside-toplevel
            evaluate_deploy_profile_consistency,
            load_deploy_profile,
        )

        try:
            _profile = load_deploy_profile(deploy_profile_id)
        except (FileNotFoundError, ValueError) as exc:
            print(f"Refusing to start: invalid ZENODEX_DEPLOY_PROFILE={deploy_profile_id!r}: {exc}")
            return 2
        _runtime_facts = {
            "sensitive_api_enabled": sensitive_api_enabled,
            "external_auth_enforced": external_auth_enforced,
            "auth_bearer_token_set": bool(auth_bearer_token),
            "allow_demo_token_auth": allow_demo_token_auth,
            "legacy_demo_token_active": legacy_demo_token_active,
            "confidential_sealed_bid_allow_in_memory_state": allow_in_memory_sealed_bid,
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
        }
        _conflicts = evaluate_deploy_profile_consistency(_profile, _runtime_facts)
        if _conflicts:
            print(
                f"Refusing to start: runtime env conflicts with deploy profile "
                f"{deploy_profile_id!r}:"
            )
            for _c in _conflicts:
                print(f"  - {_c}")
            return 2

    httpd = ThreadingHTTPServer((host, port), _Handler)
    # Attach config to server instance (used by handler).
    httpd.cors_origins = cors_origins  # type: ignore[attr-defined]
    httpd.rate_limiter = TokenBucketRateLimiter(rpm=rpm, max_buckets=max_buckets)  # type: ignore[attr-defined]
    httpd.perps_wallet_api_enabled = perps_wallet_enabled  # type: ignore[attr-defined]
    httpd.zusd_tau_wallet_api_enabled = zusd_tau_wallet_enabled  # type: ignore[attr-defined]
    httpd.zusd_monetary_wallet_api_enabled = zusd_monetary_wallet_enabled  # type: ignore[attr-defined]
    httpd.autotrader_live_api_enabled = autotrader_live_enabled  # type: ignore[attr-defined]
    httpd.autotrader_execution_keys = set()  # type: ignore[attr-defined]
    httpd.autotrader_supervisor_runs = {}  # type: ignore[attr-defined]
    httpd.autotrader_execution_lock = threading.Lock()  # type: ignore[attr-defined]
    httpd.confidential_attestation_api_enabled = confidential_attestation_enabled  # type: ignore[attr-defined]
    httpd.confidential_sealed_bid_api_enabled = confidential_sealed_bid_enabled  # type: ignore[attr-defined]
    httpd.dex_api_enabled = dex_enabled  # type: ignore[attr-defined]
    httpd.autogov_live_apply_api_enabled = autogov_live_apply_enabled  # type: ignore[attr-defined]
    httpd.demo_api_token = auth_bearer_token  # type: ignore[attr-defined]
    httpd.external_auth_enforced = external_auth_enforced  # type: ignore[attr-defined]
    httpd.confidential_feature_status = confidential_feature_status  # type: ignore[attr-defined]
    httpd.confidential_request_table = ConfidentialRequestTable()  # type: ignore[attr-defined]
    httpd.confidential_request_lock = threading.Lock()  # type: ignore[attr-defined]
    httpd.confidential_sealed_bid_table = ConfidentialSealedBidTable(  # type: ignore[attr-defined]
        state_path=confidential_sealed_bid_state_file
    )
    httpd.confidential_sealed_bid_lock = threading.Lock()  # type: ignore[attr-defined]
    confidential_sealed_bid_asset_settlement_enabled = _env_bool(
        "CONFIDENTIAL_SEALED_BID_LOCAL_LEDGER_SETTLEMENT_ENABLED",
        False,
    )
    httpd.confidential_sealed_bid_asset_settlement_submitter = (  # type: ignore[attr-defined]
        submit_confidential_sealed_bid_local_ledger_settlement
        if confidential_sealed_bid_asset_settlement_enabled
        else None
    )

    print(
        f"zenodex-api listening on http://{host}:{port} "
        f"(cors_origins={sorted(cors_origins)}, rpm={rpm}, max_buckets={max_buckets}, "
        f"perps_wallet_api={perps_wallet_enabled}, "
        f"zusd_tau_wallet_api={zusd_tau_wallet_enabled}, "
        f"zusd_monetary_wallet_api={zusd_monetary_wallet_enabled}, "
        f"autotrader_live_api={autotrader_live_enabled}, "
        f"confidential_attestation_api={confidential_attestation_enabled}, "
        f"confidential_sealed_bid_api={confidential_sealed_bid_enabled}, "
        f"confidential_sealed_bid_asset_settlement={confidential_sealed_bid_asset_settlement_enabled}, "
        f"dex_api={dex_enabled}, "
        f"autogov_live_apply_api={autogov_live_apply_enabled}, "
        f"confidential_stage={confidential_feature_status.get('stage')}, "
        f"external_auth_enforced={external_auth_enforced}, bearer_token_set={bool(auth_bearer_token)}, "
        f"legacy_demo_token_set={bool(legacy_demo_api_token)}, "
        f"demo_token_auth_allowed={allow_demo_token_auth})"
    )
    httpd.serve_forever(poll_interval=0.25)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
