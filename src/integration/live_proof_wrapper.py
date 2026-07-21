"""Fail-closed live proof-wrapper gate for mounted stream APIs."""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any, Mapping, Sequence

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .proof_verifier import ProofVerifierConfig, make_proof_verifier

LIVE_PROOF_WRAPPER_REQUEST_SCHEMA = "zenodex/live-proof-wrapper-request/v1"
LIVE_PROOF_WRAPPER_STATUS_SCHEMA = "zenodex/live-proof-wrapper-status/v1"
LIVE_PROOF_WRAPPER_HASH_DOMAIN = "zenodex.live_proof_wrapper.request/v1"
LIVE_PROOF_WRAPPER_ARTIFACT_BINDING_HASH_DOMAIN = "zenodex.live_proof_wrapper.artifact_binding/v1"
LIVE_PROOF_WRAPPER_VERIFIER_CMD_HASH_DOMAIN = "zenodex.live_proof_wrapper.verifier_cmd/v1"


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


def _load_json_object_from_env(
    *,
    json_names: Sequence[str],
    file_names: Sequence[str],
    label: str,
) -> tuple[Mapping[str, Any] | None, str | None]:
    raw_json = _first_env(json_names)
    if raw_json:
        try:
            parsed = json.loads(raw_json)
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            return None, f"{label} JSON invalid: {exc}"
        if not isinstance(parsed, Mapping):
            return None, f"{label} JSON must decode to an object"
        return parsed, None
    raw_file = _first_env(file_names)
    if not raw_file:
        return None, None
    try:
        parsed = json.loads(Path(raw_file).read_text(encoding="utf-8"))
    except OSError as exc:
        return None, f"{label} file unreadable: {exc}"
    except json.JSONDecodeError as exc:
        return None, f"{label} file JSON invalid: {exc}"
    if not isinstance(parsed, Mapping):
        return None, f"{label} file must decode to an object"
    return parsed, None


def _artifact_metadata_ready(artifact: Mapping[str, Any] | None, *, required_fields: Sequence[str]) -> bool:
    if artifact is None:
        return False
    for field in required_fields:
        if not isinstance(artifact.get(field), str) or not str(artifact.get(field)).strip():
            return False
    return True


def _hash_verifier_cmd(cmd: Sequence[str] | None) -> str | None:
    if not cmd:
        return None
    return sha256_hex(
        domain_sep_bytes(LIVE_PROOF_WRAPPER_VERIFIER_CMD_HASH_DOMAIN) + canonical_json_bytes(list(cmd))
    )


def _artifact_binding_status(
    *,
    env_prefix: str,
    verifier_cmd: Sequence[str] | None,
) -> dict[str, Any]:
    verifier_artifact, verifier_artifact_error = _load_json_object_from_env(
        json_names=(f"{env_prefix}_PROOF_VERIFIER_ARTIFACT_JSON", "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON"),
        file_names=(f"{env_prefix}_PROOF_VERIFIER_ARTIFACT_FILE", "TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE"),
        label="proof verifier artifact",
    )
    circuit_artifact, circuit_artifact_error = _load_json_object_from_env(
        json_names=(f"{env_prefix}_PROOF_CIRCUIT_ARTIFACT_JSON", "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON"),
        file_names=(f"{env_prefix}_PROOF_CIRCUIT_ARTIFACT_FILE", "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_FILE"),
        label="proof circuit artifact",
    )
    verifier_artifact_ready = _artifact_metadata_ready(verifier_artifact, required_fields=("artifact_id", "artifact_hash"))
    circuit_artifact_ready = _artifact_metadata_ready(
        circuit_artifact,
        required_fields=("artifact_id", "artifact_hash", "proof_system"),
    )
    errors: list[str] = []
    if verifier_artifact_error:
        errors.append(verifier_artifact_error)
    if circuit_artifact_error:
        errors.append(circuit_artifact_error)
    if verifier_artifact is not None and not verifier_artifact_ready:
        errors.append("proof verifier artifact missing artifact_id or artifact_hash")
    if circuit_artifact is not None and not circuit_artifact_ready:
        errors.append("proof circuit artifact missing artifact_id, artifact_hash, or proof_system")
    binding_payload = {
        "verifier_artifact": None if verifier_artifact is None else dict(verifier_artifact),
        "circuit_artifact": None if circuit_artifact is None else dict(circuit_artifact),
        "verifier_cmd_hash": _hash_verifier_cmd(verifier_cmd),
    }
    configured = verifier_artifact is not None or circuit_artifact is not None
    return {
        "configured": configured,
        "complete": verifier_artifact_ready and circuit_artifact_ready,
        "binding_hash": (
            None
            if not configured
            else sha256_hex(
                domain_sep_bytes(LIVE_PROOF_WRAPPER_ARTIFACT_BINDING_HASH_DOMAIN)
                + canonical_json_bytes(binding_payload)
            )
        ),
        "verifier_artifact": binding_payload["verifier_artifact"],
        "verifier_artifact_ready": verifier_artifact_ready,
        "circuit_artifact": binding_payload["circuit_artifact"],
        "circuit_artifact_ready": circuit_artifact_ready,
        "verifier_cmd_hash": binding_payload["verifier_cmd_hash"],
        "error": "; ".join(errors) if errors else None,
    }


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
    expected_execution_context_hash: str | None = None,
) -> dict[str, Any]:
    config = proof_verifier_config_from_env(env_prefix=env_prefix)
    artifact_binding = _artifact_binding_status(env_prefix=env_prefix, verifier_cmd=config.verifier_cmd)
    request: dict[str, Any] = {
        "schema": LIVE_PROOF_WRAPPER_REQUEST_SCHEMA,
        "surface": surface,
        "proof_intent_receipt_hash": proof_intent_receipt.get("receipt_hash"),
        "proof_intent_receipt": dict(proof_intent_receipt),
        "proof": None if proof is None else dict(proof),
    }
    if expected_execution_context_hash is not None:
        request["expected_execution_context_hash"] = expected_execution_context_hash
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
        "artifact_binding_configured": bool(artifact_binding.get("configured")),
        "artifact_binding_complete": bool(artifact_binding.get("complete")),
        "artifact_binding": artifact_binding,
        "proof_verifier": None,
        "error": None,
    }
    if proof is None:
        status["error"] = "zk_proof missing"
        return status

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
        "cmd_hash": _hash_verifier_cmd(config.verifier_cmd),
    }
    return status


def require_live_proof_wrapper(status: Mapping[str, Any]) -> None:
    if status.get("required") is True and status.get("zk_proof_verified") is not True:
        raise ValueError(f"zk_proof_required: {status.get('error') or 'proof not verified'}")
