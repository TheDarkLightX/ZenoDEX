#!/usr/bin/env python3
"""Local-testnet live proof-wrapper verifier.

This verifier is intentionally narrow: it accepts only local fixture proofs for
the live zUSD/perps wrapper request schema, then echoes the request hash and
artifact binding required by the runtime gate. It is not production proof
evidence.
"""

from __future__ import annotations

import json
import sys
from typing import Any, Mapping


def _fail(error: str) -> None:
    sys.stdout.write(json.dumps({"ok": False, "error": error}, separators=(",", ":")) + "\n")
    raise SystemExit(0)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        _fail(f"{name} must be an object")
    return value


def main() -> None:
    try:
        request = json.load(sys.stdin)
    except Exception as exc:
        _fail(f"invalid verifier request JSON: {exc}")
    req = _require_mapping(request, name="request")
    if req.get("schema") != "zenodex/live-proof-wrapper-request/v1":
        _fail("unsupported live proof-wrapper schema")
    surface = req.get("surface")
    if surface not in {"zusd_stream11", "perps_stream8"}:
        _fail("unsupported live proof-wrapper surface")
    proof = _require_mapping(req.get("proof"), name="proof")
    if proof.get("system") != "local-testnet-live-wrapper-fixture-v1":
        _fail("unsupported local fixture proof system")
    if proof.get("production_security_claim") is True:
        _fail("local fixture proof cannot make production security claim")
    verifier_request_hash = req.get("verifier_request_hash")
    if not isinstance(verifier_request_hash, str) or not verifier_request_hash:
        _fail("verifier_request_hash missing")
    out: dict[str, Any] = {
        "ok": True,
        "verifier_request_hash": verifier_request_hash,
        "surface": surface,
        "production_security_claim": False,
    }
    expected_artifact_binding = req.get("expected_artifact_binding_hash")
    if isinstance(expected_artifact_binding, str) and expected_artifact_binding:
        out["artifact_binding_hash"] = expected_artifact_binding
    sys.stdout.write(json.dumps(out, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
