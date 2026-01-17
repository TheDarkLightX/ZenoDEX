#!/usr/bin/env python3
"""
Reference proof verifier: "recompute batch" certificate (v4).

v4 keeps the projected pre-state witness (support-root commitment) from v3, but
changes the *batch commitment* to use a normalized settlement encoding. This
quotients away irrelevant list ordering in delta arrays and makes commitments
stable across equivalent encoders.

Proof schema (inside operations['3']['proof']):
  {
    "scheme": "recompute_batch_v4",
    "pre_state_commitment": "0x..",  # support root
    "batch_commitment": "0x..",
    "pre_state_snapshot_zlib_b64": "...",
    "operations_zlib_b64": "..."
  }
"""

from __future__ import annotations

import base64
import json
import sys
import zlib
from pathlib import Path
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing import compute_settlement, validate_settlement  # noqa: E402
from src.core.intent_normal_form import IntentNormalFormError, require_normal_form  # noqa: E402
from src.core.settlement_normal_form import normalize_settlement_op_for_commitment  # noqa: E402
from src.integration.dex_snapshot import state_from_snapshot  # noqa: E402
from src.integration.operations import create_settlement_operation, parse_intents, parse_settlement  # noqa: E402
from src.state.canonical import CANONICAL_ENCODING_VERSION, canonical_json_bytes, domain_sep_bytes, sha256_hex  # noqa: E402
from src.state.support_root import compute_support_state_root_for_batch  # noqa: E402

MAX_DECOMPRESSED_SNAPSHOT_BYTES = 2_000_000
MAX_DECOMPRESSED_OPERATIONS_BYTES = 2_000_000
_ZLIB_CHUNK = 4096


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


def _b64decode(value: str, *, name: str, max_chars: int = 2_500_000) -> bytes:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    if len(value) > max_chars:
        raise ValueError(f"{name} too large")
    try:
        return base64.b64decode(value.encode("ascii"), validate=True)
    except Exception as exc:
        raise ValueError(f"{name} invalid base64: {exc}") from exc


def _zlib_decompress_limited(data: bytes, *, name: str, max_out: int) -> bytes:
    if not isinstance(data, (bytes, bytearray)):
        raise TypeError(f"{name} must be bytes")
    if max_out <= 0:
        raise ValueError("max_out must be positive")

    d = zlib.decompressobj()
    out = bytearray()
    view = memoryview(data)

    for off in range(0, len(view), _ZLIB_CHUNK):
        chunk = view[off : off + _ZLIB_CHUNK]
        buf = bytes(chunk)
        while buf:
            remaining = max_out - len(out)
            if remaining <= 0:
                raise ValueError(f"{name} decompressed too large")
            out += d.decompress(buf, remaining)
            buf = d.unconsumed_tail

    remaining = max_out - len(out)
    if remaining <= 0:
        raise ValueError(f"{name} decompressed too large")
    out += d.flush(remaining)
    if len(out) > max_out:
        raise ValueError(f"{name} decompressed too large")
    if not d.eof:
        raise ValueError(f"{name} invalid zlib stream")
    return bytes(out)


def _parse_json_bytes(data: bytes, *, name: str) -> Any:
    try:
        return json.loads(data.decode("utf-8"))
    except Exception as exc:
        raise ValueError(f"{name} invalid JSON: {exc}") from exc


def _intent_signing_dict(intent: Any) -> Dict[str, Any]:
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


def _batch_commitment(signing_dicts: Sequence[Dict[str, Any]], settlement_commit_obj: Dict[str, Any]) -> str:
    payload = {
        "schema": "zenodex_batch",
        "schema_version": 1,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "intents": list(signing_dicts),
        "settlement": settlement_commit_obj,
    }
    return sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload))


def _load_witness(proof: Mapping[str, Any]) -> Tuple[Mapping[str, Any], Mapping[str, Any]]:
    if "pre_state_snapshot_zlib_b64" in proof:
        b64 = _require_str(proof.get("pre_state_snapshot_zlib_b64"), name="proof.pre_state_snapshot_zlib_b64")
        raw = _b64decode(b64, name="proof.pre_state_snapshot_zlib_b64")
        snap_bytes = _zlib_decompress_limited(raw, name="pre_state_snapshot", max_out=MAX_DECOMPRESSED_SNAPSHOT_BYTES)
        snap = _parse_json_bytes(snap_bytes, name="pre_state_snapshot")
    else:
        snap = proof.get("pre_state_snapshot")
    snapshot = _require_mapping(snap, name="proof.pre_state_snapshot")

    if "operations_zlib_b64" in proof:
        b64 = _require_str(proof.get("operations_zlib_b64"), name="proof.operations_zlib_b64")
        raw = _b64decode(b64, name="proof.operations_zlib_b64")
        ops_bytes = _zlib_decompress_limited(raw, name="operations", max_out=MAX_DECOMPRESSED_OPERATIONS_BYTES)
        ops = _parse_json_bytes(ops_bytes, name="operations")
    else:
        ops = proof.get("operations")
    operations = _require_mapping(ops, name="proof.operations")

    return snapshot, operations


def _verify(payload: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
    schema = payload.get("schema")
    if schema != "zenodex_proof":
        return False, "unsupported schema"
    version = payload.get("schema_version")
    if version != 1:
        return False, "unsupported schema_version"

    proof = _require_mapping(payload.get("proof"), name="proof")
    scheme = _require_str(proof.get("scheme"), name="proof.scheme")
    if scheme != "recompute_batch_v4":
        return False, "unsupported proof scheme"

    pre_state_commitment = _require_str(payload.get("pre_state_commitment"), name="pre_state_commitment")
    batch_commitment = _require_str(payload.get("batch_commitment"), name="batch_commitment")

    proof_pre = _require_str(proof.get("pre_state_commitment"), name="proof.pre_state_commitment")
    proof_batch = _require_str(proof.get("batch_commitment"), name="proof.batch_commitment")
    if proof_pre != pre_state_commitment:
        return False, "proof/pre_state_commitment mismatch"
    if proof_batch != batch_commitment:
        return False, "proof/batch_commitment mismatch"

    snapshot, operations = _load_witness(proof)

    try:
        state = state_from_snapshot(snapshot)
    except Exception as exc:
        return False, f"invalid pre_state_snapshot: {exc}"

    try:
        intents = parse_intents(dict(operations))
        claimed_settlement = parse_settlement(dict(operations))
    except Exception as exc:
        return False, f"invalid operations: {exc}"
    if claimed_settlement is None:
        return False, "missing settlement"

    try:
        require_normal_form(intents, strict_lp_order=False)
    except IntentNormalFormError as exc:
        return False, f"intents not in normal form: {exc}"

    try:
        computed_pre = compute_support_state_root_for_batch(
            intents=intents,
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
        )
    except Exception as exc:
        return False, f"failed to compute support root: {exc}"
    if computed_pre != pre_state_commitment:
        return False, "pre_state_commitment does not match snapshot"

    try:
        signing_dicts = [_intent_signing_dict(i) for i in intents]
        claimed_op3 = create_settlement_operation(claimed_settlement).get("3")
        if not isinstance(claimed_op3, dict):
            raise TypeError("settlement operation must be an object")
        settlement_commit_obj = normalize_settlement_op_for_commitment(claimed_op3)
        computed_batch = _batch_commitment(signing_dicts, settlement_commit_obj)
    except Exception as exc:
        return False, f"failed to compute batch_commitment: {exc}"
    if computed_batch != batch_commitment:
        return False, "batch_commitment does not match embedded witness"

    try:
        recomputed = compute_settlement(
            intents=intents,
            pools=state.pools,
            balances=state.balances,
            lp_balances=state.lp_balances,
        )
    except Exception as exc:
        return False, f"settlement recomputation failed: {exc}"

    ok, err = validate_settlement(recomputed, state.balances, state.pools, state.lp_balances)
    if not ok:
        return False, f"recomputed settlement invalid: {err or 'rejected'}"

    try:
        claimed_norm = normalize_settlement_op_for_commitment(create_settlement_operation(claimed_settlement)["3"])
        recomputed_norm = normalize_settlement_op_for_commitment(create_settlement_operation(recomputed)["3"])
    except Exception as exc:
        return False, f"failed to compare settlements: {exc}"

    if claimed_norm != recomputed_norm:
        return False, "settlement mismatch"

    return True, None


def main(argv: Sequence[str]) -> None:
    _ = argv
    try:
        payload = json.loads(sys.stdin.buffer.read() or b"{}")
    except Exception as exc:
        _fail(f"invalid JSON input: {exc}")
    if not isinstance(payload, dict):
        _fail("payload must be an object")

    ok, err = _verify(payload)
    if not ok:
        _fail(err or "invalid")
    _ok()


if __name__ == "__main__":
    main(sys.argv[1:])

