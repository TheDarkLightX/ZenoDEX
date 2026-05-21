"""Fail-closed live proof-wrapper gate for mounted stream APIs."""

from __future__ import annotations

import json
import os
from typing import Any, Mapping, Sequence

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .proof_verifier import ProofVerifierConfig, make_proof_verifier


LIVE_PROOF_WRAPPER_REQUEST_SCHEMA = "zenodex/live-proof-wrapper-request/v1"
LIVE_PROOF_WRAPPER_STATUS_SCHEMA = "zenodex/live-proof-wrapper-status/v1"
LIVE_PROOF_WRAPPER_HASH_DOMAIN = "zenodex.live_proof_wrapper.request/v1"


def _env_bool(name: str, default: bool = False) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    return raw.strip().lower() in {"1", "true", "yes", "on"}


def _env_float(name: str, default: float, *, lo: float, hi: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return float(default)
    try:
        value = float(raw.strip())
    except Exception:
        return float(default)
    return min(max(value, lo), hi)


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        value = int(raw.strip())
    except Exception:
        return int(default)
    return min(max(value, lo), hi)


def _first_env(names: Sequence[str]) -> str:
    for name in names:
        raw = os.environ.get(name, "").strip()
        if raw:
            return raw
    return ""


def _parse_cmd_json(raw: str, *, name: str) -> list[str] | None:
    if not raw:
        return None
    obj = json.loads(raw)
    if not isinstance(obj, list) or not obj:
        raise ValueError(f"{name} must be a non-empty JSON array")
    cmd: list[str] = []
    for index, item in enumerate(obj):
        if not isinstance(item, str) or not item:
            raise ValueError(f"{name}[{index}] must be a non-empty string")
        cmd.append(item)
    return cmd


def live_zk_proof_required(*, env_prefix: str) -> bool:
    return _env_bool(f"{env_prefix}_REQUIRE_ZK_PROOF", _env_bool("TAU_DEX_REQUIRE_LIVE_ZK_PROOF", False))


def proof_from_request(body: Mapping[str, Any]) -> Mapping[str, Any] | None:
    raw = body.get("zk_proof")
    if raw is None:
        raw = body.get("proof")
    if raw is None:
        return None
    if not isinstance(raw, Mapping):
        raise ValueError("zk_proof must be an object")
    return raw


def proof_verifier_config_from_env(*, env_prefix: str) -> ProofVerifierConfig:
    cmd_raw = _first_env((f"{env_prefix}_PROOF_VERIFIER_CMD_JSON", "TAU_DEX_PROOF_VERIFIER_CMD_JSON"))
    cmd = _parse_cmd_json(
        cmd_raw,
        name=f"{env_prefix}_PROOF_VERIFIER_CMD_JSON" if cmd_raw == os.environ.get(f"{env_prefix}_PROOF_VERIFIER_CMD_JSON", "").strip() else "TAU_DEX_PROOF_VERIFIER_CMD_JSON",
    )
    timeout_s = _env_float(
        f"{env_prefix}_PROOF_VERIFIER_TIMEOUT_S",
        _env_float("TAU_DEX_PROOF_VERIFIER_TIMEOUT_S", 10.0, lo=0.1, hi=120.0),
        lo=0.1,
        hi=120.0,
    )
    max_proof_bytes = _env_int(
        f"{env_prefix}_PROOF_VERIFIER_MAX_PROOF_BYTES",
        _env_int("TAU_DEX_PROOF_VERIFIER_MAX_PROOF_BYTES", 256_000, lo=1024, hi=5_000_000),
        lo=1024,
        hi=5_000_000,
    )
    allow_path_lookup = _env_bool(
        f"{env_prefix}_PROOF_VERIFIER_ALLOW_PATH_LOOKUP",
        _env_bool("TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP", False),
    )
    return ProofVerifierConfig(
        enabled=bool(cmd),
        verifier_cmd=cmd,
        allow_path_lookup=allow_path_lookup,
        timeout_s=timeout_s,
        max_proof_bytes=max_proof_bytes,
    )


def _hash_request(request: Mapping[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(LIVE_PROOF_WRAPPER_HASH_DOMAIN) + canonical_json_bytes(dict(request)))


def verify_live_proof_wrapper(
    *,
    surface: str,
    env_prefix: str,
    proof_intent_receipt: Mapping[str, Any],
    proof: Mapping[str, Any] | None,
    required: bool,
) -> dict[str, Any]:
    request: dict[str, Any] = {
        "schema": LIVE_PROOF_WRAPPER_REQUEST_SCHEMA,
        "surface": surface,
        "proof_intent_receipt_hash": proof_intent_receipt.get("receipt_hash"),
        "proof_intent_receipt": dict(proof_intent_receipt),
        "proof": None if proof is None else dict(proof),
    }
    request_hash = _hash_request(request)
    status: dict[str, Any] = {
        "schema": LIVE_PROOF_WRAPPER_STATUS_SCHEMA,
        "surface": surface,
        "required": bool(required),
        "proof_provided": proof is not None,
        "verifier_configured": False,
        "zk_proof_verified": False,
        "proof_intent_receipt_hash": proof_intent_receipt.get("receipt_hash"),
        "verifier_request_hash": request_hash,
        "proof_verifier": None,
        "error": None,
    }
    if proof is None:
        status["error"] = "zk_proof missing"
        return status

    config = proof_verifier_config_from_env(env_prefix=env_prefix)
    status["verifier_configured"] = bool(config.enabled)
    if not config.enabled:
        status["error"] = "proof verifier disabled"
        return status

    verifier = make_proof_verifier(config)
    ok, error = verifier.verify(request)
    status["zk_proof_verified"] = bool(ok)
    status["error"] = error
    status["proof_verifier"] = {
        "kind": "subprocess",
        "allow_path_lookup": bool(config.allow_path_lookup),
        "timeout_s": float(config.timeout_s),
        "max_proof_bytes": int(config.max_proof_bytes),
    }
    return status


def require_live_proof_wrapper(status: Mapping[str, Any]) -> None:
    if status.get("required") is True and status.get("zk_proof_verified") is not True:
        raise ValueError(f"zk_proof_required: {status.get('error') or 'proof not verified'}")
