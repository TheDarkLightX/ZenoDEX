#!/usr/bin/env python3
"""Strict live proof-wrapper verifier for perps NP RISC0 receipts.

This command is intended for `PERPS_WALLET_PROOF_VERIFIER_CMD_JSON`. It accepts
the runtime live-wrapper request, verifies the embedded RISC0 receipt through the
Rust CLI, and binds the verified journal to the runtime proof-intent receipt.

It only covers `risc0.zenodex_perps_np_transition.v1`.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex  # noqa: E402

PROOF_TYPE = "risc0.zenodex_perps_np_transition.v1"
RECEIPT_HASH_DOMAIN = "zenodex.perps_wallet.proof_intent_receipt/v1"
WRAPPER_SCHEMA = "zenodex/live-proof-wrapper-request/v1"
SURFACE = PROOF_TYPE
LIVE_SURFACE_ALIASES = {SURFACE, "perps_stream8"}


def _fail(error: str) -> None:
    sys.stdout.write(json.dumps({"ok": False, "error": error}, separators=(",", ":")) + "\n")
    raise SystemExit(0)


def _mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        _fail(f"{name} must be an object")
    return value


def _str(value: Any, *, name: str, required: bool = True) -> str | None:
    if value is None and not required:
        return None
    if not isinstance(value, str) or not value.strip():
        _fail(f"{name} must be a non-empty string")
    return value.strip()


def _normalize_hex(value: str) -> str:
    raw = value.strip().lower()
    if raw.startswith("0x"):
        raw = raw[2:]
    if len(raw) != 64:
        _fail("hex binding must be 64 chars")
    try:
        bytes.fromhex(raw)
    except ValueError:
        _fail("hex binding is invalid")
    return raw


def _cli_cmd() -> list[str]:
    raw_json = os.environ.get("RISC0_PERPS_NP_CLI_CMD_JSON", "").strip()
    if raw_json:
        try:
            parsed = json.loads(raw_json)
        except json.JSONDecodeError as exc:
            _fail(f"RISC0_PERPS_NP_CLI_CMD_JSON invalid: {exc}")
        if not isinstance(parsed, list) or not parsed or not all(isinstance(x, str) and x for x in parsed):
            _fail("RISC0_PERPS_NP_CLI_CMD_JSON must be a non-empty string array")
        return list(parsed)
    raw_bin = os.environ.get("RISC0_PERPS_NP_CLI_BIN", "").strip()
    if raw_bin:
        return [raw_bin]
    release_bin = ROOT / "zk" / "state_proof_risc0" / "target" / "release" / "tau-state-proof-risc0-cli"
    debug_bin = ROOT / "zk" / "state_proof_risc0" / "target" / "debug" / "tau-state-proof-risc0-cli"
    if release_bin.exists():
        return [str(release_bin)]
    if debug_bin.exists():
        return [str(debug_bin)]
    _fail("RISC0 perps NP verifier CLI missing; set RISC0_PERPS_NP_CLI_BIN")


def _required_hash(expected: Mapping[str, Any], key: str) -> str:
    return _normalize_hex(_str(expected.get(key), name=f"proof.expected.{key}"))


def _hash_payload(domain: str, payload: Mapping[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(domain) + canonical_json_bytes(dict(payload)))


def _actions_from_proof(proof: Mapping[str, Any], expected: Mapping[str, Any]) -> list[Any]:
    actions = proof.get("actions")
    if actions is None:
        actions = expected.get("actions")
    if not isinstance(actions, list) or not actions:
        _fail("proof.actions must be a non-empty list for strict RISC0 perps NP verification")
    return list(actions)


def _run_cli_verify(
    proof: Mapping[str, Any],
    expected: Mapping[str, Any],
    actions: list[Any],
    trusted_execution_context_hash: str,
) -> Mapping[str, Any]:
    state_hash = _normalize_hex(_str(proof.get("state_hash"), name="proof.state_hash"))
    chain_id = _str(expected.get("chain_id"), name="proof.expected.chain_id")
    pre_app_hash = _required_hash(expected, "pre_app_hash")
    post_app_hash = _required_hash(expected, "post_app_hash")
    request = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": state_hash,
        "chain_id": chain_id,
        "proof": dict(proof),
        "tau_state": {"app_hash": post_app_hash},
        "context": {
            "chain_id": chain_id,
            "execution_context_hash": trusted_execution_context_hash,
            "app_hash_pre": pre_app_hash,
            "operation_hash": _required_hash(expected, "operation_hash"),
            "state_delta_hash": _required_hash(expected, "state_delta_hash"),
            "oracle_binding_hash": _required_hash(expected, "oracle_binding_hash"),
            "collateral_binding_hash": _required_hash(expected, "collateral_binding_hash"),
            "participant_set_hash": _required_hash(expected, "participant_set_hash"),
            "receipt_root": _required_hash(expected, "receipt_root"),
        },
        "actions": actions,
    }
    timeout = float(os.environ.get("RISC0_PERPS_NP_VERIFY_TIMEOUT_S", "60"))
    try:
        proc = subprocess.run(
            _cli_cmd()
            + [
                "--expected-execution-context-hash",
                trusted_execution_context_hash,
            ],
            input=json.dumps(request, separators=(",", ":")),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=str(ROOT),
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        _fail("RISC0 perps NP verifier timed out")
    except Exception as exc:  # noqa: BLE001
        _fail(f"RISC0 perps NP verifier error: {exc}")
    if proc.returncode != 0:
        _fail(f"RISC0 perps NP verifier exited {proc.returncode}: {proc.stderr.strip()[-300:]}")
    try:
        out = json.loads(proc.stdout)
    except json.JSONDecodeError:
        _fail("RISC0 perps NP verifier returned invalid JSON")
    if not isinstance(out, Mapping):
        _fail("RISC0 perps NP verifier returned non-object JSON")
    return out


def _expected_from_proof(proof: Mapping[str, Any]) -> dict[str, Any]:
    source = proof.get("expected")
    if source is None:
        source = proof.get("meta")
    expected = _mapping(source, name="proof.expected or proof.meta")
    return dict(expected)


def _bind_runtime_receipt(expected: dict[str, Any], receipt: Mapping[str, Any]) -> None:
    body = _mapping(receipt.get("body"), name="proof_intent_receipt.body")
    if body.get("schema") != "zenodex/perps_wallet/proof_intent_receipt/v1":
        _fail("unsupported proof intent receipt schema")
    action = _str(body.get("action"), name="proof_intent_receipt.body.action")
    if action not in {"run_epoch", "settle_epoch"}:
        _fail("RISC0 perps NP proof only covers run_epoch/settle_epoch transitions")
    expected["proof_type"] = PROOF_TYPE
    expected["chain_id"] = _str(body.get("chain_id"), name="proof_intent_receipt.body.chain_id")
    expected["market_id"] = _str(body.get("market_id"), name="proof_intent_receipt.body.market_id")
    expected["operation_hash"] = _normalize_hex(_str(body.get("operation_hash"), name="proof_intent_receipt.body.operation_hash"))

    # The verifier boundary must be anchored to the runtime receipt, not to
    # proof metadata supplied by the same untrusted request.
    expected["pre_app_hash"] = _normalize_hex(
        _str(body.get("app_hash_before"), name="proof_intent_receipt.body.app_hash_before")
    )
    expected["post_app_hash"] = _normalize_hex(
        _str(body.get("app_hash_after"), name="proof_intent_receipt.body.app_hash_after")
    )

    proof_state_delta_witness_hash = expected.get("state_delta_witness_hash")
    receipt_state_delta_witness_hash = body.get("state_delta_witness_hash")
    if receipt_state_delta_witness_hash is not None:
        receipt_witness_hash = _normalize_hex(
            _str(receipt_state_delta_witness_hash, name="proof_intent_receipt.body.state_delta_witness_hash")
        )
        proof_witness_hash = _normalize_hex(
            _str(proof_state_delta_witness_hash, name="proof.expected.state_delta_witness_hash")
        )
        if proof_witness_hash != receipt_witness_hash:
            _fail("state_delta_witness_hash mismatch")
        expected["state_delta_witness_hash"] = receipt_witness_hash
    elif proof_state_delta_witness_hash is not None:
        _fail("state_delta_witness_hash mismatch")


def _verify_runtime_receipt_hash(req: Mapping[str, Any], receipt: Mapping[str, Any]) -> None:
    body = _mapping(receipt.get("body"), name="proof_intent_receipt.body")
    computed_hash = _hash_payload(RECEIPT_HASH_DOMAIN, body)
    receipt_hash = _str(receipt.get("receipt_hash"), name="proof_intent_receipt.receipt_hash")
    if receipt_hash != computed_hash:
        _fail("proof_intent_receipt.receipt_hash mismatch")
    if req.get("proof_intent_receipt_hash") != computed_hash:
        _fail("proof_intent_receipt_hash mismatch")


def main() -> None:
    try:
        request = json.load(sys.stdin)
    except Exception as exc:  # noqa: BLE001
        _fail(f"invalid verifier request JSON: {exc}")
    req = _mapping(request, name="request")
    if req.get("schema") != WRAPPER_SCHEMA:
        _fail("unsupported live proof-wrapper schema")
    request_surface = req.get("surface")
    if request_surface not in LIVE_SURFACE_ALIASES:
        _fail("unsupported live proof-wrapper surface")
    verifier_request_hash = _str(req.get("verifier_request_hash"), name="verifier_request_hash")
    receipt = _mapping(req.get("proof_intent_receipt"), name="proof_intent_receipt")
    _verify_runtime_receipt_hash(req, receipt)

    proof = _mapping(req.get("proof"), name="proof")
    if proof.get("production_security_claim") is True:
        _fail("RISC0 perps NP verifier cannot make production security claim")
    if proof.get("proof_type") != PROOF_TYPE:
        _fail("unsupported proof_type")
    _str(proof.get("proof"), name="proof.proof")

    expected = _expected_from_proof(proof)
    trusted_execution_context_hash = _normalize_hex(
        _str(
            req.get("expected_execution_context_hash"),
            name="expected_execution_context_hash",
        )
    )
    if _required_hash(expected, "execution_context_hash") != trusted_execution_context_hash:
        _fail("proof execution_context_hash mismatch")
    _bind_runtime_receipt(expected, receipt)
    actions = _actions_from_proof(proof, expected)
    verify_out = _run_cli_verify(
        proof,
        expected,
        actions,
        trusted_execution_context_hash,
    )
    if verify_out.get("ok") is not True:
        _fail(f"RISC0 perps NP proof rejected: {verify_out.get('error') or 'unknown error'}")

    out: dict[str, Any] = {
        "ok": True,
        "verifier_request_hash": verifier_request_hash,
        "surface": request_surface,
        "verified_surface": SURFACE,
        "proof_type": PROOF_TYPE,
        "production_security_claim": False,
    }
    if isinstance(expected.get("risc0_image_id"), str):
        out["risc0_image_id"] = expected["risc0_image_id"]
    artifact_binding = req.get("expected_artifact_binding_hash")
    if isinstance(artifact_binding, str) and artifact_binding:
        out["artifact_binding_hash"] = artifact_binding
    sys.stdout.write(json.dumps(out, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
