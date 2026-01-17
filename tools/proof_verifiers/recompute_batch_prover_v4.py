#!/usr/bin/env python3
"""
Reference proof producer for the recompute-batch scheme (v4).

v4 matches `recompute_batch_v4.py`:
  - pre_state_commitment is a support root (projected pre-state),
  - the embedded snapshot witness is projected to the batch's support, and
  - batch_commitment uses a normalized settlement encoding (quotients list order).
"""

from __future__ import annotations

import base64
import json
import sys
import zlib
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from src.core.intent_normal_form import IntentNormalFormError, require_normal_form  # noqa: E402
from src.core.settlement_normal_form import normalize_settlement_op_for_commitment  # noqa: E402
from src.integration.dex_snapshot import DEX_SNAPSHOT_VERSION, state_from_snapshot  # noqa: E402
from src.integration.operations import create_settlement_operation, parse_intents, parse_settlement  # noqa: E402
from src.state.canonical import CANONICAL_ENCODING_VERSION, canonical_json_bytes, domain_sep_bytes, sha256_hex  # noqa: E402
from src.state.support_root import (  # noqa: E402
    BatchStateSupport,
    compute_support_state_root,
    derive_batch_state_support,
)


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


def _batch_commitment(signing_dicts: Sequence[Dict[str, Any]], settlement_commit_obj: Dict[str, Any]) -> str:
    payload = {
        "schema": "zenodex_batch",
        "schema_version": 1,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "intents": list(signing_dicts),
        "settlement": settlement_commit_obj,
    }
    return sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload))


def _compress_b64(value: Any) -> str:
    raw = canonical_json_bytes(value)
    comp = zlib.compress(raw, level=9)
    return base64.b64encode(comp).decode("ascii")


def _project_snapshot(state: Any, support: BatchStateSupport) -> Dict[str, Any]:
    balances_entries = []
    for pubkey, asset in support.balance_keys:
        amount = state.balances.get(pubkey, asset)
        if amount == 0:
            continue
        balances_entries.append({"pubkey": pubkey, "asset": asset, "amount": int(amount)})
    balances_entries.sort(key=lambda e: (e["pubkey"], e["asset"]))

    pools_entries = []
    for pool_id in support.pool_ids:
        pool = state.pools.get(pool_id)
        if pool is None:
            continue
        pools_entries.append(
            {
                "pool_id": pool_id,
                "asset0": pool.asset0,
                "asset1": pool.asset1,
                "reserve0": int(pool.reserve0),
                "reserve1": int(pool.reserve1),
                "fee_bps": int(pool.fee_bps),
                "lp_supply": int(pool.lp_supply),
                "status": pool.status.value,
                "created_at": int(pool.created_at),
            }
        )
    pools_entries.sort(key=lambda e: e["pool_id"])

    lp_entries = []
    for pubkey, pool_id in support.lp_keys:
        amount = state.lp_balances.get(pubkey, pool_id)
        if amount == 0:
            continue
        lp_entries.append({"pubkey": pubkey, "pool_id": pool_id, "amount": int(amount)})
    lp_entries.sort(key=lambda e: (e["pubkey"], e["pool_id"]))

    fee_acc = state.fee_accumulator
    fee_acc_obj: Dict[str, Any] = {"dust": int(getattr(fee_acc, "dust", 0))}

    vault_obj = None
    if getattr(state, "vault", None) is not None:
        v = state.vault
        vault_obj = {
            "acc_reward_per_share": int(v.acc_reward_per_share),
            "last_update_acc": int(v.last_update_acc),
            "pending_rewards": int(v.pending_rewards),
            "reward_balance": int(v.reward_balance),
            "staked_lp_shares": int(v.staked_lp_shares),
        }

    oracle_obj = None
    if getattr(state, "oracle", None) is not None:
        o = state.oracle
        oracle_obj = {"price_timestamp": int(o.price_timestamp), "max_staleness_seconds": int(o.max_staleness_seconds)}

    return {
        "version": DEX_SNAPSHOT_VERSION,
        "balances": balances_entries,
        "pools": pools_entries,
        "lp_balances": lp_entries,
        "fee_accumulator": fee_acc_obj,
        "vault": vault_obj,
        "oracle": oracle_obj,
    }


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

        intents = parse_intents(dict(ops))
        settlement = parse_settlement(dict(ops))
        if settlement is None:
            raise ValueError("missing settlement")

        require_normal_form(intents, strict_lp_order=False)

        support = derive_batch_state_support(intents, pools=state.pools)
        pre_state_commitment = compute_support_state_root(
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
            support=support,
        )

        projected_snapshot = _project_snapshot(state, support)

        signing_dicts = [_intent_signing_dict(i) for i in intents]
        settlement_op3 = create_settlement_operation(settlement).get("3")
        if not isinstance(settlement_op3, dict):
            raise TypeError("settlement operation must be an object")
        settlement_commit_obj = normalize_settlement_op_for_commitment(settlement_op3)
        batch_commitment = _batch_commitment(signing_dicts, settlement_commit_obj)
    except IntentNormalFormError as exc:
        _die(f"intents not in normal form: {exc}")
    except Exception as exc:
        _die(f"failed to build proof: {exc}")

    proof = {
        "scheme": "recompute_batch_v4",
        "pre_state_commitment": pre_state_commitment,
        "batch_commitment": batch_commitment,
        "pre_state_snapshot_zlib_b64": _compress_b64(projected_snapshot),
        "operations_zlib_b64": _compress_b64(dict(ops)),
    }
    sys.stdout.write(json.dumps(proof, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main(sys.argv[1:])

