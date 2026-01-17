#!/usr/bin/env python3

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_testnet_dex_plugin import apply_app_tx


def _now() -> int:
    return int(time.time())


def main() -> int:
    sender_pubkey = "00" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    os.environ.setdefault("TAU_DEX_FAUCET", "1")
    os.environ.setdefault("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    os.environ.setdefault("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    os.environ.setdefault("TAU_DEX_CHAIN_ID", "tau-local")

    create_pool = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": _now() + 3600,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    ok, state_json, _app_hash, _patch, err = apply_app_tx(
        app_state_json="",
        chain_balances={sender_pubkey: 0},
        operations={"4": {"mint": [[sender_pubkey, asset0, 10_000], [sender_pubkey, asset1, 10_000]]}, "2": [create_pool]},
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=_now(),
    )
    if not ok:
        print(f"[offline-demo] FAIL (create pool): {err}")
        return 1

    state = json.loads(state_json)
    pool = state["pools"][0]
    pool_id = pool["pool_id"]
    print(f"[offline-demo] pool_id={pool_id}")
    print(f"[offline-demo] pool reserves after create: reserve0={pool['reserve0']} reserve1={pool['reserve1']} fee_bps={pool['fee_bps']}")

    balances = {(b["pubkey"], b["asset"]): b["amount"] for b in state.get("balances", [])}
    before_in = int(balances.get((sender_pubkey, asset0), 0))
    before_out = int(balances.get((sender_pubkey, asset1), 0))
    print(f"[offline-demo] balances before swap: in={before_in} out={before_out}")

    swap = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": _now() + 3600,
        "pool_id": pool_id,
        "asset_in": asset0,
        "asset_out": asset1,
        "amount_in": 100,
        "min_amount_out": 1,
        "recipient": sender_pubkey,
    }

    ok2, state_json2, _app_hash2, _patch2, err2 = apply_app_tx(
        app_state_json=state_json,
        chain_balances={sender_pubkey: 0},
        operations={"2": [swap]},
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=_now() + 1,
    )
    if not ok2:
        print(f"[offline-demo] FAIL (swap): {err2}")
        return 1

    state2 = json.loads(state_json2)
    pool2 = [p for p in state2["pools"] if p.get("pool_id") == pool_id][0]
    print(f"[offline-demo] pool reserves after swap:   reserve0={pool2['reserve0']} reserve1={pool2['reserve1']}")

    balances2 = {(b["pubkey"], b["asset"]): b["amount"] for b in state2.get("balances", [])}
    after_in = int(balances2.get((sender_pubkey, asset0), 0))
    after_out = int(balances2.get((sender_pubkey, asset1), 0))
    print(f"[offline-demo] balances after swap:  in={after_in} out={after_out}")
    print(f"[offline-demo] deltas: d_in={after_in - before_in} d_out={after_out - before_out}")
    print("[offline-demo] OK: swap executed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
