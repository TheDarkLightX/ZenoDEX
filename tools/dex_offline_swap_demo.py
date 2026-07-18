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

from src.core.consensus_time import (  # noqa: E402
    clock_policy_schedule_hash_v1,
    default_height_only_clock_schedule_v1,
    verify_execution_clock_v1,
)
from src.core.generic_token_authority import (  # noqa: E402
    GenericTokenAssetAuthority,
    GenericTokenAuthorityState,
)
from src.integration.tau_testnet_dex_plugin import (  # noqa: E402
    apply_app_tx,
    build_zusd_policy_bound_genesis_app_state,
)
from src.integration.zusd_monetary_bridge import ZUSDMonetaryConfig  # noqa: E402


def _now() -> int:
    return int(time.time())


def _execution_clock(*, chain_id: str, height: int):
    schedule = default_height_only_clock_schedule_v1(chain_id=chain_id)
    return verify_execution_clock_v1(
        chain_id=chain_id,
        height=height,
        schedule=schedule,
        expected_schedule_hash=clock_policy_schedule_hash_v1(schedule),
    )


def main() -> int:
    chain_id = "tau-local"
    sender_pubkey = "0x" + "00" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    os.environ.setdefault("TAU_DEX_FAUCET", "1")
    os.environ.setdefault("TAU_DEX_REQUIRE_INTENT_SIGS", "0")
    os.environ.setdefault("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")
    os.environ.setdefault("TAU_DEX_CHAIN_ID", chain_id)

    registrations = tuple(
        sorted(
            (
                GenericTokenAssetAuthority(
                    asset_id=asset,
                    total_supply_units=0,
                    mint_authority_pubkey=sender_pubkey,
                )
                for asset in (asset0, asset1)
            ),
            key=lambda registration: registration.asset_id,
        )
    )
    genesis_state_json, _genesis_hash = build_zusd_policy_bound_genesis_app_state(
        config=ZUSDMonetaryConfig(chain_id=chain_id),
        generic_token_authority=GenericTokenAuthorityState(assets=registrations),
    )

    create_pool = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": sender_pubkey,
        "nonce": 1,
        "deadline": _now() + 3600,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }

    ok, state_json, _app_hash, _patch, err = apply_app_tx(
        app_state_json=genesis_state_json,
        chain_balances={sender_pubkey: 0},
        operations={
            "7": {"mint": [[sender_pubkey, asset0, 10_000], [sender_pubkey, asset1, 10_000]]},
            "5": [create_pool],
        },
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=0,
        execution_clock=_execution_clock(chain_id=chain_id, height=0),
    )
    if not ok:
        print(f"[offline-demo] FAIL (create pool): {err}")
        return 1

    state = json.loads(state_json)
    dex_state = state.get("dex_state", state)
    pool = dex_state["pools"][0]
    pool_id = pool["pool_id"]
    print(f"[offline-demo] pool_id={pool_id}")
    print(
        f"[offline-demo] pool reserves after create: reserve0={pool['reserve0']} reserve1={pool['reserve1']} fee_bps={pool['fee_bps']}"
    )

    balances = {(b["pubkey"], b["asset"]): b["amount"] for b in dex_state.get("balances", [])}
    before_in = int(balances.get((sender_pubkey, asset0), 0))
    before_out = int(balances.get((sender_pubkey, asset1), 0))
    print(f"[offline-demo] balances before swap: in={before_in} out={before_out}")

    swap = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": sender_pubkey,
        "nonce": 2,
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
        operations={"5": [swap]},
        tx_sender_pubkey=sender_pubkey,
        block_timestamp=1,
        execution_clock=_execution_clock(chain_id=chain_id, height=1),
    )
    if not ok2:
        print(f"[offline-demo] FAIL (swap): {err2}")
        return 1

    state2 = json.loads(state_json2)
    dex_state2 = state2.get("dex_state", state2)
    pool2 = [p for p in dex_state2["pools"] if p.get("pool_id") == pool_id][0]
    print(
        f"[offline-demo] pool reserves after swap:   reserve0={pool2['reserve0']} reserve1={pool2['reserve1']}"
    )

    balances2 = {(b["pubkey"], b["asset"]): b["amount"] for b in dex_state2.get("balances", [])}
    after_in = int(balances2.get((sender_pubkey, asset0), 0))
    after_out = int(balances2.get((sender_pubkey, asset1), 0))
    print(f"[offline-demo] balances after swap:  in={after_in} out={after_out}")
    print(f"[offline-demo] deltas: d_in={after_in - before_in} d_out={after_out - before_out}")
    print("[offline-demo] OK: swap executed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
