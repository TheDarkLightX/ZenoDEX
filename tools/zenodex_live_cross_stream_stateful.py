#!/usr/bin/env python3
"""Deterministic stateful replay for live zUSD-to-perps app-bridge surfaces.

The campaign exercises the mounted live transaction lanes used by the browser:

- stream 11: collateralized zUSD monetary actions;
- stream 9: transferable zUSD token transport;
- stream 8: clearinghouse perps collateral and settlement actions.

It is intentionally bounded and deterministic. Passing this tool is a receipt
for the named disaster states under these scenarios, not a broad safety proof.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.zusd import E8  # noqa: E402
from src.integration import tau_testnet_dex_plugin as plugin  # noqa: E402
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine  # noqa: E402
from src.integration.zusd_monetary_bridge import stability_pool_pubkey  # noqa: E402
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id  # noqa: E402


SCHEMA = "zenodex.live_cross_stream_stateful_replay.v1"
CHAIN_ID = "tau-local-zusd-perps-stateful"
DEADLINE = 999_999_999

ORACLE_PRIVKEY = 81
ALICE_PRIVKEY = 82
BOB_PRIVKEY = 83
OPERATOR_PRIVKEY = 84

ORACLE = "0x" + bls_pubkey_hex_from_privkey(ORACLE_PRIVKEY)
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
BOB = "0x" + bls_pubkey_hex_from_privkey(BOB_PRIVKEY)
OPERATOR = "0x" + bls_pubkey_hex_from_privkey(OPERATOR_PRIVKEY)


@contextmanager
def _patched_env(values: Mapping[str, str]):
    old = {key: os.environ.get(key) for key in values}
    try:
        for key, value in values.items():
            os.environ[key] = value
        yield
    finally:
        for key, value in old.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


def _base_env(*, require_oracle_adapter: bool = False) -> dict[str, str]:
    env = {
        "TAU_DEX_CHAIN_ID": CHAIN_ID,
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": ORACLE,
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY": OPERATOR,
        "TAU_DEX_PERP_ORACLE_PUBKEY": ORACLE,
        "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH": "0",
    }
    if require_oracle_adapter:
        env["TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH"] = "1"
    return env


def _signed_init_market(*, market_id: str, nonce_a: int = 1, nonce_b: int = 1) -> dict[str, Any]:
    op: dict[str, Any] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "init_market_2p",
        "quote_asset": derive_zusd_tau_asset_id(chain_id=CHAIN_ID),
        "account_a_pubkey": ALICE,
        "account_b_pubkey": BOB,
        "deadline": DEADLINE,
        "nonce_a": int(nonce_a),
        "nonce_b": int(nonce_b),
    }
    op["sig_a"] = sign_perp_op_for_engine(
        op,
        privkey=ALICE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ALICE,
        nonce=nonce_a,
    )
    op["sig_b"] = sign_perp_op_for_engine(
        op,
        privkey=BOB_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=BOB,
        nonce=nonce_b,
    )
    return op


def _signed_publish_price(*, market_id: str, price_e8: int, oracle_nonce: int) -> dict[str, Any]:
    op: dict[str, Any] = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": "publish_clearing_price",
        "price_e8": int(price_e8),
        "deadline": DEADLINE,
        "oracle_nonce": int(oracle_nonce),
    }
    op["oracle_sig"] = sign_perp_op_for_engine(
        op,
        privkey=ORACLE_PRIVKEY,
        chain_id=CHAIN_ID,
        signer_pubkey=ORACLE,
        nonce=oracle_nonce,
    )
    return op


def _apply(
    app_state_json: str,
    *,
    operations: Mapping[str, object],
    sender: str,
    block_timestamp: int,
    chain_balances: Mapping[str, int] | None = None,
) -> tuple[bool, str, str | None]:
    ok, next_json, _hash, _patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={} if chain_balances is None else dict(chain_balances),
        operations=dict(operations),
        tx_sender_pubkey=sender,
        block_timestamp=int(block_timestamp),
    )
    return bool(ok), str(next_json), err


def _expect_ok(
    app_state_json: str,
    *,
    operations: Mapping[str, object],
    sender: str,
    block_timestamp: int,
    chain_balances: Mapping[str, int] | None = None,
) -> str:
    ok, next_json, err = _apply(
        app_state_json,
        operations=operations,
        sender=sender,
        block_timestamp=block_timestamp,
        chain_balances=chain_balances,
    )
    if not ok:
        raise AssertionError(err or "operation rejected")
    return next_json


def _expect_reject_unchanged(
    app_state_json: str,
    *,
    operations: Mapping[str, object],
    sender: str,
    block_timestamp: int,
    expected_error_fragment: str,
    chain_balances: Mapping[str, int] | None = None,
) -> str:
    ok, next_json, err = _apply(
        app_state_json,
        operations=operations,
        sender=sender,
        block_timestamp=block_timestamp,
        chain_balances=chain_balances,
    )
    if ok:
        raise AssertionError("operation unexpectedly accepted")
    if next_json != app_state_json:
        raise AssertionError("rejected operation mutated app_state_json")
    if expected_error_fragment not in (err or ""):
        raise AssertionError(f"unexpected error {err!r}; expected fragment {expected_error_fragment!r}")
    return err or ""


def _state_obj(app_state_json: str) -> dict[str, Any]:
    obj = json.loads(app_state_json)
    if not isinstance(obj, dict):
        raise AssertionError("app state must decode to object")
    return obj


def _dex_state(obj: Mapping[str, Any]) -> Mapping[str, Any]:
    dex_state = obj.get("dex_state", obj)
    if not isinstance(dex_state, Mapping):
        raise AssertionError("dex_state must be object")
    return dex_state


def _balance(obj: Mapping[str, Any], *, pubkey: str, asset: str) -> int:
    for row in _dex_state(obj).get("balances", []):
        if not isinstance(row, Mapping):
            continue
        if row.get("pubkey") == pubkey and row.get("asset") == asset:
            return int(row.get("amount", 0))
    return 0


def _market(obj: Mapping[str, Any], *, market_id: str) -> Mapping[str, Any]:
    perps = _dex_state(obj).get("perps", {})
    if not isinstance(perps, Mapping):
        raise AssertionError("perps state must be object")
    for market in perps.get("markets", []):
        if isinstance(market, Mapping) and market.get("market_id") == market_id:
            return market
    raise AssertionError(f"market not found: {market_id}")


def _seed_minted_state() -> tuple[str, dict[str, int]]:
    chain_balances = {ALICE: 20 * E8}
    app = ""
    app = _expect_ok(
        app,
        operations={"11": [{"module": "ZUSDFinance", "action": "bootstrap_oracle", "price_e8": 100 * E8, "nonce": 1, "deadline": DEADLINE}]},
        sender=ORACLE,
        block_timestamp=1,
        chain_balances=chain_balances,
    )
    app = _expect_ok(
        app,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "deposit_collateral",
                    "owner_pubkey": ALICE,
                    "amount_e8": 20 * E8,
                    "nonce": 1,
                    "deadline": DEADLINE,
                }
            ]
        },
        sender=ALICE,
        block_timestamp=2,
        chain_balances=chain_balances,
    )
    chain_balances = {ALICE: 0}
    app = _expect_ok(
        app,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "mint_zusd",
                    "owner_pubkey": ALICE,
                    "amount_e8": 1_000 * E8,
                    "nonce": 2,
                    "deadline": DEADLINE,
                }
            ]
        },
        sender=ALICE,
        block_timestamp=3,
        chain_balances=chain_balances,
    )
    return app, chain_balances


def _seed_market_state(*, market_id: str) -> str:
    app, chain_balances = _seed_minted_state()
    app = _expect_ok(
        app,
        operations={
            "9": [
                {
                    "module": "TauToken",
                    "action": "transfer",
                    "asset": derive_zusd_tau_asset_id(chain_id=CHAIN_ID),
                    "sender_pubkey": ALICE,
                    "to_pubkey": BOB,
                    "amount": 400,
                    "nonce": 1,
                    "deadline": DEADLINE,
                }
            ]
        },
        sender=ALICE,
        block_timestamp=4,
        chain_balances=chain_balances,
    )
    app = _expect_ok(
        app,
        operations={"8": [_signed_init_market(market_id=market_id)]},
        sender=OPERATOR,
        block_timestamp=5,
        chain_balances=chain_balances,
    )
    return app


def _scenario_happy_path() -> dict[str, Any]:
    market_id = "perp:ch2p:stateful-happy"
    app = _seed_market_state(market_id=market_id)
    for sender, amount, timestamp in ((ALICE, 250, 6), (BOB, 300, 7)):
        app = _expect_ok(
            app,
            operations={
                "8": [
                    {
                        "module": "TauPerp",
                        "version": "1.0",
                        "market_id": market_id,
                        "action": "deposit_collateral",
                        "account_pubkey": sender,
                        "amount": amount,
                    }
                ]
            },
            sender=sender,
            block_timestamp=timestamp,
            chain_balances={ALICE: 0},
        )

    obj = _state_obj(app)
    zusd_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    market = _market(obj, market_id=market_id)
    market_state = market["state"]
    assert _balance(obj, pubkey=ALICE, asset=zusd_asset) == 350
    assert _balance(obj, pubkey=BOB, asset=zusd_asset) == 100
    assert _balance(obj, pubkey=stability_pool_pubkey(chain_id=CHAIN_ID), asset=zusd_asset) == 0
    assert market["quote_asset"] == zusd_asset
    assert int(market_state["collateral_e8_a"]) == 250 * E8
    assert int(market_state["collateral_e8_b"]) == 300 * E8
    assert int(obj["zusd_monetary"]["core"]["debt_e8"]) == 1_000 * E8
    return {
        "market_id": market_id,
        "alice_zusd_balance": 350,
        "bob_zusd_balance": 100,
        "collateral_e8_a": int(market_state["collateral_e8_a"]),
        "collateral_e8_b": int(market_state["collateral_e8_b"]),
    }


def _scenario_duplicate_zusd_replay() -> dict[str, Any]:
    app, chain_balances = _seed_minted_state()
    err = _expect_reject_unchanged(
        app,
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "mint_zusd",
                    "owner_pubkey": ALICE,
                    "amount_e8": 1_000 * E8,
                    "nonce": 2,
                    "deadline": DEADLINE,
                }
            ]
        },
        sender=ALICE,
        block_timestamp=4,
        expected_error_fragment="nonce invalid",
        chain_balances=chain_balances,
    )
    return {"rejection": err}


def _scenario_cross_stream_atomicity() -> dict[str, Any]:
    err = _expect_reject_unchanged(
        "",
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                    "deadline": DEADLINE,
                }
            ],
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": "perp:ch2p:missing",
                    "action": "deposit_collateral",
                    "account_pubkey": ORACLE,
                    "amount": 1,
                }
            ],
        },
        sender=ORACLE,
        block_timestamp=1,
        expected_error_fragment="unknown market_id",
    )
    return {"rejection": err}


def _scenario_expired_zusd_deadline() -> dict[str, Any]:
    err = _expect_reject_unchanged(
        "",
        operations={
            "11": [
                {
                    "module": "ZUSDFinance",
                    "action": "bootstrap_oracle",
                    "price_e8": 100 * E8,
                    "nonce": 1,
                    "deadline": 1,
                }
            ]
        },
        sender=ORACLE,
        block_timestamp=2,
        expected_error_fragment="deadline expired",
        chain_balances={ALICE: 20 * E8},
    )
    return {"rejection": err}


def _scenario_perps_overdeposit_rejected() -> dict[str, Any]:
    market_id = "perp:ch2p:stateful-overdeposit"
    app = _seed_market_state(market_id=market_id)
    err = _expect_reject_unchanged(
        app,
        operations={
            "8": [
                {
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": market_id,
                    "action": "deposit_collateral",
                    "account_pubkey": ALICE,
                    "amount": 10_000,
                }
            ]
        },
        sender=ALICE,
        block_timestamp=6,
        expected_error_fragment="insufficient balance",
        chain_balances={ALICE: 0},
    )
    return {"rejection": err}


def _scenario_settle_requires_oracle_bridge() -> dict[str, Any]:
    market_id = "perp:ch2p:stateful-oracle-required"
    app = _seed_market_state(market_id=market_id)
    app = _expect_ok(
        app,
        operations={"8": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "advance_epoch", "delta": 1}]},
        sender=OPERATOR,
        block_timestamp=6,
        chain_balances={ALICE: 0},
    )
    app = _expect_ok(
        app,
        operations={"8": [_signed_publish_price(market_id=market_id, price_e8=E8, oracle_nonce=1)]},
        sender=ORACLE,
        block_timestamp=7,
        chain_balances={ALICE: 0},
    )
    err = _expect_reject_unchanged(
        app,
        operations={"8": [{"module": "TauPerp", "version": "1.0", "market_id": market_id, "action": "settle_epoch"}]},
        sender=OPERATOR,
        block_timestamp=8,
        expected_error_fragment="settle_epoch requires oracle_adapter_bridge",
        chain_balances={ALICE: 0},
    )
    return {"rejection": err}


SCENARIOS: tuple[tuple[str, str, Callable[[], dict[str, Any]], bool], ...] = (
    (
        "happy_path_zusd_to_perps_collateral_conserves",
        "balance_drift_after_cross_stream_success",
        _scenario_happy_path,
        False,
    ),
    (
        "duplicate_zusd_mint_replay_rejected_without_side_effect",
        "duplicate_side_effect_after_replay",
        _scenario_duplicate_zusd_replay,
        False,
    ),
    (
        "cross_stream_valid_zusd_bad_perps_is_atomic",
        "cross_stream_partial_mutation",
        _scenario_cross_stream_atomicity,
        False,
    ),
    (
        "expired_zusd_deadline_rejected_without_side_effect",
        "expired_deadline_materializes",
        _scenario_expired_zusd_deadline,
        False,
    ),
    (
        "perps_overdeposit_rejected_without_balance_loss",
        "perps_overdeposit_materializes",
        _scenario_perps_overdeposit_rejected,
        False,
    ),
    (
        "settle_epoch_requires_oracle_bridge_without_side_effect",
        "stale_or_missing_oracle_evidence_settles",
        _scenario_settle_requires_oracle_bridge,
        True,
    ),
)


def run_campaign() -> dict[str, Any]:
    scenarios: list[dict[str, Any]] = []
    with _patched_env(_base_env()):
        for scenario_id, disaster_state, fn, require_oracle_adapter in SCENARIOS:
            env = _base_env(require_oracle_adapter=require_oracle_adapter)
            with _patched_env(env):
                try:
                    evidence = fn()
                    scenarios.append(
                        {
                            "id": scenario_id,
                            "status": "accepted",
                            "disaster_state": disaster_state,
                            "evidence": evidence,
                        }
                    )
                except Exception as exc:
                    scenarios.append(
                        {
                            "id": scenario_id,
                            "status": "failed",
                            "disaster_state": disaster_state,
                            "error": str(exc),
                        }
                    )
    accepted = sum(1 for scenario in scenarios if scenario["status"] == "accepted")
    return {
        "schema": SCHEMA,
        "ok": accepted == len(scenarios),
        "chain_id": CHAIN_ID,
        "surface": "stream11_zusd_monetary__stream9_zusd_token__stream8_clearinghouse_perps",
        "scenario_count": len(scenarios),
        "accepted_scenario_count": accepted,
        "disaster_states": [scenario["disaster_state"] for scenario in scenarios],
        "scenarios": scenarios,
        "not_claimed": [
            "production_wallet_key_management",
            "live_tau_fee_market_model",
            "exhaustive_cross_stream_state_space",
            "production_oracle_truth",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "pretty"), default="pretty")
    parser.add_argument("--output", help="optional output path for the replay receipt JSON")
    args = parser.parse_args(argv)

    receipt = run_campaign()
    text = json.dumps(receipt, indent=2 if args.format == "pretty" else None, sort_keys=True)
    if args.output:
        Path(args.output).write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
