#!/usr/bin/env python3
"""
Reference proof *producer* for the recompute-batch scheme (v1).

This script builds a proof object that:
  - binds to the engine's pre_state_commitment (state_root),
  - binds to the engine's batch_commitment (intents + settlement commitment),
  - embeds the public inputs needed by the verifier (snapshot + ops).

Input (stdin): JSON object with keys:
  - pre_state_snapshot: DexSnapshot-like object (see src/integration/dex_snapshot.py)
  - operations: {"2": [...], "3": {...}} where "3" is settlement op WITHOUT proof

Output (stdout): JSON proof object to attach under operations["3"]["proof"].
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from src.core.intent_normal_form import IntentNormalFormError, require_normal_form  # noqa: E402
from src.integration.dex_snapshot import state_from_snapshot  # noqa: E402
from src.integration.operations import create_settlement_operation, parse_intents, parse_settlement  # noqa: E402
from src.state.canonical import CANONICAL_ENCODING_VERSION, canonical_json_bytes, domain_sep_bytes, sha256_hex  # noqa: E402
from src.state.state_root import compute_state_root  # noqa: E402


def _die(msg: str) -> None:
    sys.stderr.write(str(msg) + "\n")
    raise SystemExit(2)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    return value


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


def _settlement_commitment_dict(settlement_obj: Any) -> Dict[str, Any]:
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


def main(argv: Sequence[str]) -> None:
    _ = argv
    try:
        raw = json.loads(sys.stdin.buffer.read() or b"{}")
        if not isinstance(raw, dict):
            raise ValueError("input must be an object")
        snapshot = _require_mapping(raw.get("pre_state_snapshot"), name="pre_state_snapshot")
        ops = _require_mapping(raw.get("operations"), name="operations")
    except Exception as exc:
        _die(f"invalid input: {exc}")

    try:
        state = state_from_snapshot(snapshot)
        pre_state_commitment = compute_state_root(balances=state.balances, pools=state.pools, lp_balances=state.lp_balances)
        intents = parse_intents(dict(ops))
        settlement = parse_settlement(dict(ops))
        if settlement is None:
            raise ValueError("missing settlement")
        require_normal_form(intents, strict_lp_order=False)
        signing_dicts = [_intent_signing_dict(i) for i in intents]
        settlement_commit_obj = _settlement_commitment_dict(settlement)
        batch_commitment = _batch_commitment(signing_dicts, settlement_commit_obj)
    except IntentNormalFormError as exc:
        _die(f"intents not in normal form: {exc}")
    except Exception as exc:
        _die(f"failed to build proof: {exc}")

    proof = {
        "scheme": "recompute_batch_v1",
        "pre_state_commitment": pre_state_commitment,
        "batch_commitment": batch_commitment,
        "pre_state_snapshot": snapshot,
        "operations": dict(ops),
    }
    sys.stdout.write(json.dumps(proof, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main(sys.argv[1:])

