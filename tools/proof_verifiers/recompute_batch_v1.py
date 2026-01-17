#!/usr/bin/env python3
"""
Reference proof verifier: "recompute batch" certificate (v1).

This is *not* a ZK system. It is a pragmatic R&D step that enables:
  - proof-carrying settlement plumbing end-to-end, and
  - enforcement of intent normal forms (canonical batch ordering),
by packaging the public inputs (pre-state snapshot + batch ops) inside the proof
and re-running the functional-core settlement computation.

Expected verifier input (stdin): canonical JSON with keys:
  - schema: "zenodex_proof"
  - schema_version: 1
  - proof: object (opaque to the engine)
  - pre_state_commitment: 0x-prefixed hex
  - batch_commitment: 0x-prefixed hex

The engine (src/integration/dex_engine.py) already fail-closed binds the proof's
top-level commitments. This verifier additionally checks that the embedded
witness matches those commitments and that recomputation matches the committed
settlement.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing import compute_settlement, validate_settlement  # noqa: E402
from src.core.intent_normal_form import IntentNormalFormError, require_normal_form  # noqa: E402
from src.integration.dex_snapshot import state_from_snapshot  # noqa: E402
from src.integration.operations import create_settlement_operation, parse_intents, parse_settlement  # noqa: E402
from src.state.canonical import CANONICAL_ENCODING_VERSION, canonical_json_bytes, domain_sep_bytes, sha256_hex  # noqa: E402
from src.state.state_root import compute_state_root  # noqa: E402


def _fail(msg: str) -> None:
    sys.stdout.write(json.dumps({"ok": False, "error": str(msg)}, separators=(",", ":")) + "\n")
    raise SystemExit(0)


def _ok() -> None:
    sys.stdout.write(json.dumps({"ok": True}, separators=(",", ":")) + "\n")
    raise SystemExit(0)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _intent_signing_dict(intent: Any) -> Dict[str, Any]:
    # Mirrors src/integration/dex_engine._intent_signing_dict().
    fields = dict(getattr(intent, "fields", None) or {})
    d: Dict[str, Any] = {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": intent.deadline,
        "fields": fields,
    }
    if getattr(intent, "salt", None) is not None:
        d["salt"] = intent.salt
    return d


def _settlement_commitment_dict(settlement_obj: Any) -> Dict[str, Any]:
    """
    Mirrors src/integration/dex_engine._settlement_commitment_dict().

    Accepts either:
    - a parsed Settlement object
    - a dict matching operations['3'] (already without proof)
    """
    if isinstance(settlement_obj, Mapping):
        op3 = dict(settlement_obj)
    else:
        op3 = create_settlement_operation(settlement_obj).get("3")
        if not isinstance(op3, dict):
            raise TypeError("settlement operation must be an object")

    out: Dict[str, Any] = {k: v for k, v in op3.items() if k not in ("batch_ref", "events")}

    fills = out.get("fills")
    if not isinstance(fills, list):
        raise TypeError("settlement.fills must be a list")

    compact_fills = []
    for fill in fills:
        if not isinstance(fill, Mapping):
            raise TypeError("fill must be an object")
        compact_fills.append({k: v for k, v in fill.items() if v is not None and k != "reason"})
    out["fills"] = compact_fills
    return out


def _batch_commitment(signing_dicts: Sequence[Dict[str, Any]], settlement_commit_obj: Dict[str, Any]) -> str:
    payload = {
        "schema": "zenodex_batch",
        "schema_version": 1,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "intents": list(signing_dicts),
        "settlement": settlement_commit_obj,
    }
    return sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload))


def _parse_payload(stdin_bytes: bytes) -> Dict[str, Any]:
    try:
        obj = json.loads(stdin_bytes)
    except Exception as exc:
        raise ValueError(f"invalid JSON input: {exc}") from exc
    if not isinstance(obj, dict):
        raise ValueError("payload must be an object")
    return obj


def _verify(payload: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
    schema = payload.get("schema")
    if schema != "zenodex_proof":
        return False, "unsupported schema"
    version = payload.get("schema_version")
    if version != 1:
        return False, "unsupported schema_version"

    proof = _require_mapping(payload.get("proof"), name="proof")
    scheme = _require_str(proof.get("scheme"), name="proof.scheme")
    if scheme != "recompute_batch_v1":
        return False, "unsupported proof scheme"

    pre_state_commitment = _require_str(payload.get("pre_state_commitment"), name="pre_state_commitment")
    batch_commitment = _require_str(payload.get("batch_commitment"), name="batch_commitment")

    # Engine already enforced the binding of these fields inside `proof`, but we
    # re-check to keep the verifier standalone.
    proof_pre = _require_str(proof.get("pre_state_commitment"), name="proof.pre_state_commitment")
    proof_batch = _require_str(proof.get("batch_commitment"), name="proof.batch_commitment")
    if proof_pre != pre_state_commitment:
        return False, "proof/pre_state_commitment mismatch"
    if proof_batch != batch_commitment:
        return False, "proof/batch_commitment mismatch"

    snapshot = _require_mapping(proof.get("pre_state_snapshot"), name="proof.pre_state_snapshot")
    ops = _require_mapping(proof.get("operations"), name="proof.operations")

    # Parse and reconstruct pre-state.
    try:
        state = state_from_snapshot(snapshot)
    except Exception as exc:
        return False, f"invalid pre_state_snapshot: {exc}"

    # Validate pre-state commitment matches.
    try:
        computed_pre = compute_state_root(balances=state.balances, pools=state.pools, lp_balances=state.lp_balances)
    except Exception as exc:
        return False, f"failed to compute state_root: {exc}"
    if computed_pre != pre_state_commitment:
        return False, "pre_state_commitment does not match snapshot"

    # Parse intents + claimed settlement.
    try:
        intents = parse_intents(dict(ops))
    except Exception as exc:
        return False, f"invalid intents: {exc}"
    try:
        claimed_settlement = parse_settlement(dict(ops))
    except Exception as exc:
        return False, f"invalid settlement: {exc}"
    if claimed_settlement is None:
        return False, "missing settlement"

    # Enforce canonical intent ordering (normal form) when a proof is present.
    try:
        require_normal_form(intents, strict_lp_order=False)
    except IntentNormalFormError as exc:
        return False, f"intents not in normal form: {exc}"

    # Ensure commitments recompute from embedded witness.
    try:
        signing_dicts = [_intent_signing_dict(i) for i in intents]
        settlement_commit_obj = _settlement_commitment_dict(create_settlement_operation(claimed_settlement)["3"])
        computed_batch = _batch_commitment(signing_dicts, settlement_commit_obj)
    except Exception as exc:
        return False, f"failed to compute batch_commitment: {exc}"
    if computed_batch != batch_commitment:
        return False, "batch_commitment does not match embedded witness"

    # Recompute settlement and compare commitment-relevant fields.
    try:
        recomputed = compute_settlement(intents=intents, pools=state.pools, balances=state.balances, lp_balances=state.lp_balances)
    except Exception as exc:
        return False, f"settlement recomputation failed: {exc}"

    ok, err = validate_settlement(recomputed, state.balances, state.pools, state.lp_balances)
    if not ok:
        return False, f"recomputed settlement invalid: {err or 'rejected'}"

    try:
        claimed_commit = _settlement_commitment_dict(create_settlement_operation(claimed_settlement)["3"])
        recomputed_commit = _settlement_commitment_dict(create_settlement_operation(recomputed)["3"])
    except Exception as exc:
        return False, f"failed to compare settlements: {exc}"

    if claimed_commit != recomputed_commit:
        return False, "settlement mismatch"

    return True, None


def main(argv: Sequence[str]) -> None:
    _ = argv
    stdin_bytes = sys.stdin.buffer.read()
    try:
        payload = _parse_payload(stdin_bytes)
    except Exception as exc:
        _fail(str(exc))

    ok, err = _verify(payload)
    if not ok:
        _fail(err or "invalid")
    _ok()


if __name__ == "__main__":
    main(sys.argv[1:])

