#!/usr/bin/env python3
"""Deterministic stateful replay for live ZenoDEX app/API surfaces.

The campaign exercises the mounted live transaction lanes used by the browser:

- stream 11: collateralized zUSD monetary actions;
- stream 9: transferable zUSD token transport;
- stream 8: clearinghouse perps collateral and settlement actions.
- AutoTrader explicit local/testnet execute-once request consumption.
- confidential extension attestation live-admission request consumption.
- confidential bounded runtime-receipt execution request consumption.

It is intentionally bounded and deterministic. Passing this tool is a receipt
for the named disaster states under these scenarios, not a broad safety proof.
"""

from __future__ import annotations

# ruff: noqa: E402,I001

import argparse
import json
import os
import random
import sys
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.confidential_extension_live_admission import (
    validate_confidential_extension_live_admission,  # noqa: E402
)
from src.core.confidential_extension_receipts import (
    make_confidential_extension_receipt,  # noqa: E402
)
from src.core.zusd import E8  # noqa: E402
from src.integration import autotrader_live_api  # noqa: E402
from src.integration import tau_testnet_dex_plugin as plugin  # noqa: E402
from src.integration.confidential_runtime_receipts import (
    build_confidential_runtime_execution_receipt_v1,  # noqa: E402
)
from src.integration.tau_net_client import (  # noqa: E402
    bls_pubkey_hex_from_privkey,
    sign_perp_op_for_engine,
)
from src.integration.zusd_monetary_bridge import stability_pool_pubkey  # noqa: E402
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id  # noqa: E402
from src.state.confidential_requests import (  # noqa: E402
    ConfidentialRequestKey,
    ConfidentialRequestTable,
)

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
PARTICIPANTS = (ALICE, BOB)

CONF_NITRO_PCR0 = "a" * 96
CONF_NITRO_PCR8 = "b" * 96
CONF_POLICY_DIGEST = "0x" + ("d" * 64)
CONF_OTHER_POLICY_DIGEST = "0x" + ("e" * 64)
CONF_MEASUREMENT = f"nitro:pcr0:{CONF_NITRO_PCR0}:pcr8:{CONF_NITRO_PCR8}"
CONF_APPROVED_MEASUREMENTS = {CONF_MEASUREMENT}
CONF_STATUS_HASH = "0x" + ("1" * 64)
CONF_ALLOWLIST_HASH = "0x" + ("2" * 64)
CONF_VERIFIER_BINDING_HASH = "0x" + ("3" * 64)


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


def _sp_deposit(obj: Mapping[str, Any], *, pubkey: str) -> int:
    monetary = obj.get("zusd_monetary")
    if not isinstance(monetary, Mapping):
        return 0
    deposits = monetary.get("sp_deposits", [])
    if not isinstance(deposits, list):
        raise AssertionError("sp_deposits must be a list")
    for row in deposits:
        if isinstance(row, Mapping) and row.get("pubkey") == pubkey:
            return int(row.get("amount_e8", 0))
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


def _token_transfer(*, sender: str, receiver: str, amount: int, nonce: int) -> dict[str, Any]:
    return {
        "module": "TauToken",
        "action": "transfer",
        "asset": derive_zusd_tau_asset_id(chain_id=CHAIN_ID),
        "sender_pubkey": sender,
        "to_pubkey": receiver,
        "amount": int(amount),
        "nonce": int(nonce),
        "deadline": DEADLINE,
    }


def _perp_collateral_op(*, market_id: str, action: str, account: str, amount: int) -> dict[str, Any]:
    return {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": market_id,
        "action": action,
        "account_pubkey": account,
        "amount": int(amount),
    }


def _zusd_sp_op(*, action: str, account: str, amount: int, nonce: int, deadline: int = DEADLINE) -> dict[str, Any]:
    return {
        "module": "ZUSDFinance",
        "action": action,
        "account_pubkey": account,
        "amount_e8": int(amount) * E8,
        "nonce": int(nonce),
        "deadline": int(deadline),
    }


def _confidential_receipt(*, request_id: str = "req-conf-live-1") -> dict[str, Any]:
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id=request_id,
        policy_version="tee-policy-v1",
        policy_digest=CONF_POLICY_DIGEST,
        measurement=CONF_MEASUREMENT,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=9,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )


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


def _scenario_confidential_admission_replay() -> dict[str, Any]:
    receipt = _confidential_receipt()
    empty_table = ConfidentialRequestTable()

    ok, err, used_table = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=CONF_APPROVED_MEASUREMENTS,
        expected_policy_digest=CONF_POLICY_DIGEST,
        request_table=empty_table,
    )
    if not ok or used_table is None:
        raise AssertionError(err or "first confidential admission rejected")

    replay_ok, replay_err, replay_table = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=CONF_APPROVED_MEASUREMENTS,
        expected_policy_digest=CONF_POLICY_DIGEST,
        request_table=used_table,
    )
    if replay_ok or replay_table is not None:
        raise AssertionError("confidential request replay unexpectedly admitted")
    if replay_err != "request_replay":
        raise AssertionError(f"unexpected confidential replay error: {replay_err!r}")

    mismatch_ok, mismatch_err, mismatch_table = validate_confidential_extension_live_admission(
        receipt=_confidential_receipt(request_id="req-conf-policy-mismatch"),
        approved_measurements=CONF_APPROVED_MEASUREMENTS,
        expected_policy_digest=CONF_OTHER_POLICY_DIGEST,
        request_table=ConfidentialRequestTable(),
    )
    if mismatch_ok or mismatch_table is not None:
        raise AssertionError("confidential policy mismatch consumed a request")
    if mismatch_err != "policy_digest_mismatch":
        raise AssertionError(f"unexpected confidential policy error: {mismatch_err!r}")

    return {
        "first_admission": "accepted",
        "replay_rejection": replay_err,
        "policy_mismatch_rejection": mismatch_err,
        "used_request_count": len(used_table.get_all()),
    }


def _scenario_confidential_runtime_execute_replay() -> dict[str, Any]:
    receipt = _confidential_receipt(request_id="req-conf-runtime-1")
    request_table = ConfidentialRequestTable()

    ok, err, _updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=CONF_APPROVED_MEASUREMENTS,
        expected_policy_digest=CONF_POLICY_DIGEST,
        request_table=request_table,
    )
    if not ok:
        raise AssertionError(err or "confidential runtime admission rejected")

    try:
        build_confidential_runtime_execution_receipt_v1(
            receipt=receipt,
            execution_id="exec runtime bad",
            execution_kind="private_route_quote",
            result_code="bounded_route_selected",
            operator_status_hash=CONF_STATUS_HASH,
            approved_measurements_hash=CONF_ALLOWLIST_HASH,
            external_verifier_binding_hash=CONF_VERIFIER_BINDING_HASH,
        )
    except ValueError as exc:
        bad_runtime_error = str(exc)
    else:
        raise AssertionError("bad confidential runtime execution unexpectedly accepted")

    retry_ok, retry_err, _retry_updated = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=CONF_APPROVED_MEASUREMENTS,
        expected_policy_digest=CONF_POLICY_DIGEST,
        request_table=request_table,
    )
    if not retry_ok:
        raise AssertionError(retry_err or "confidential runtime request was consumed before execution")

    runtime_receipt = build_confidential_runtime_execution_receipt_v1(
        receipt=receipt,
        execution_id="exec-conf-runtime-1",
        execution_kind="private_route_quote",
        result_code="bounded_route_selected",
        operator_status_hash=CONF_STATUS_HASH,
        approved_measurements_hash=CONF_ALLOWLIST_HASH,
        external_verifier_binding_hash=CONF_VERIFIER_BINDING_HASH,
    )
    request_table.mark_used(
        ConfidentialRequestKey(
            extension_id="route-premium-v1",
            provider_id="provider-1",
            request_id="req-conf-runtime-1",
        )
    )

    replay_ok, replay_err, replay_table = validate_confidential_extension_live_admission(
        receipt=receipt,
        approved_measurements=CONF_APPROVED_MEASUREMENTS,
        expected_policy_digest=CONF_POLICY_DIGEST,
        request_table=request_table,
    )
    if replay_ok or replay_table is not None:
        raise AssertionError("confidential runtime replay unexpectedly admitted")
    if replay_err != "request_replay":
        raise AssertionError(f"unexpected confidential runtime replay error: {replay_err!r}")

    return {
        "bad_runtime_error": bad_runtime_error,
        "retry_after_bad_runtime": "accepted",
        "runtime_receipt_hash": runtime_receipt["receipt_hash"],
        "replay_rejection": replay_err,
        "used_request_count": len(request_table.get_all()),
    }


def _scenario_autotrader_execute_once_replay() -> dict[str, Any]:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []
        sequence = 9
        fail_next_send = True

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return type(self).sequence

        def sendtx(self, payload: object) -> str:
            if type(self).fail_next_send:
                type(self).fail_next_send = False
                return "ERROR: temporary mempool outage"
            if not isinstance(payload, dict):
                raise AssertionError("AutoTrader sent non-object Tau payload")
            type(self).sent.append(dict(payload))
            type(self).sequence += 1
            return "SUCCESS: Transaction queued."

    body = {
        "execution_id": "stateful-exec-1",
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": CHAIN_ID,
        "tx_sequence_number": 9,
        "tx_expiration_time": DEADLINE,
        "last_used_nonce": 0,
    }
    execution_keys: set[str] = set()
    old_client = autotrader_live_api.TauNetTcpClient
    _FakeTauClient.sent = []
    _FakeTauClient.sequence = 9
    _FakeTauClient.fail_next_send = True

    with _patched_env(
        {
            "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING": "true",
            "AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION": "true",
            "AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED": "true",
            "AUTOTRADER_LIVE_CHAIN_ID": CHAIN_ID,
        }
    ):
        autotrader_live_api.TauNetTcpClient = _FakeTauClient  # type: ignore[assignment]
        try:
            failed_status, failed = autotrader_live_api.handle_autotrader_live_request(
                "POST",
                "/api/strategy/autotrader/execute-once",
                json.dumps(body).encode("utf-8"),
                execution_keys=execution_keys,
            )
            if failed_status != 400 or failed.get("error") != "sendtx_failed":
                raise AssertionError(f"unexpected AutoTrader first failure: {failed_status} {failed!r}")
            if execution_keys:
                raise AssertionError("AutoTrader execute-once key was consumed after failed send")
            if _FakeTauClient.sent:
                raise AssertionError("AutoTrader failed send recorded a queued payload")

            accepted_status, accepted = autotrader_live_api.handle_autotrader_live_request(
                "POST",
                "/api/strategy/autotrader/execute-once",
                json.dumps(body).encode("utf-8"),
                execution_keys=execution_keys,
            )
            if accepted_status != 200 or accepted.get("ok") is not True:
                raise AssertionError(f"unexpected AutoTrader acceptance: {accepted_status} {accepted!r}")
            if execution_keys != {"stateful-exec-1"}:
                raise AssertionError("AutoTrader execute-once key was not consumed after success")
            if len(_FakeTauClient.sent) != 1:
                raise AssertionError("AutoTrader successful execute-once did not send exactly once")

            replay_body = {**body, "tx_sequence_number": 10}
            replay_status, replay = autotrader_live_api.handle_autotrader_live_request(
                "POST",
                "/api/strategy/autotrader/execute-once",
                json.dumps(replay_body).encode("utf-8"),
                execution_keys=execution_keys,
            )
            if replay_status != 400 or replay.get("error") != "execution_replay":
                raise AssertionError(f"unexpected AutoTrader replay response: {replay_status} {replay!r}")
            if len(_FakeTauClient.sent) != 1:
                raise AssertionError("AutoTrader replay sent a second transaction")
        finally:
            autotrader_live_api.TauNetTcpClient = old_client  # type: ignore[assignment]

    return {
        "first_failure": failed["error"],
        "key_count_after_failed_send": 0,
        "success_status": accepted["status"],
        "replay_rejection": replay["error"],
        "sent_count": len(_FakeTauClient.sent),
    }


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
    (
        "confidential_live_admission_replay_rejected_without_double_consume",
        "duplicate_confidential_admission_after_replay",
        _scenario_confidential_admission_replay,
        False,
    ),
    (
        "confidential_runtime_execute_replay_rejected_without_double_consume",
        "duplicate_confidential_runtime_after_replay",
        _scenario_confidential_runtime_execute_replay,
        False,
    ),
    (
        "autotrader_execute_once_replay_rejected_without_second_send",
        "autotrader_execute_once_replay_or_failure_key_burn",
        _scenario_autotrader_execute_once_replay,
        False,
    ),
)


def _assert_fuzz_state(app_state_json: str, model: Mapping[str, Any], *, market_id: str) -> None:
    obj = _state_obj(app_state_json)
    zusd_asset = derive_zusd_tau_asset_id(chain_id=CHAIN_ID)
    market = _market(obj, market_id=market_id)
    market_state = market["state"]
    balances = model["balances"]
    perps_collateral = model["perps_collateral"]
    sp_deposits = model["sp_deposits"]

    assert _balance(obj, pubkey=ALICE, asset=zusd_asset) == int(balances[ALICE])
    assert _balance(obj, pubkey=BOB, asset=zusd_asset) == int(balances[BOB])
    assert _balance(obj, pubkey=stability_pool_pubkey(chain_id=CHAIN_ID), asset=zusd_asset) == int(
        sum(sp_deposits.values())
    )
    assert _sp_deposit(obj, pubkey=ALICE) == int(sp_deposits[ALICE]) * E8
    assert _sp_deposit(obj, pubkey=BOB) == int(sp_deposits[BOB]) * E8
    assert int(market_state["collateral_e8_a"]) == int(perps_collateral[ALICE]) * E8
    assert int(market_state["collateral_e8_b"]) == int(perps_collateral[BOB]) * E8

    total_zusd = (
        int(balances[ALICE])
        + int(balances[BOB])
        + int(sp_deposits[ALICE])
        + int(sp_deposits[BOB])
        + int(perps_collateral[ALICE])
        + int(perps_collateral[BOB])
    )
    if total_zusd != 1_000:
        raise AssertionError(f"zUSD conservation drift: {total_zusd}")


def _run_fuzz_seed(*, seed: int, steps: int) -> dict[str, Any]:
    rng = random.Random(seed)
    market_id = f"perp:ch2p:fuzz-{seed}"
    app = _seed_market_state(market_id=market_id)
    model: dict[str, Any] = {
        "balances": {ALICE: 600, BOB: 400},
        "perps_collateral": {ALICE: 0, BOB: 0},
        "sp_deposits": {ALICE: 0, BOB: 0},
        "token_nonce": {ALICE: 1, BOB: 0},
        "zusd_nonce": {ALICE: 2, BOB: 0},
    }
    _assert_fuzz_state(app, model, market_id=market_id)

    accepted = 0
    rejected = 0
    action_counts: dict[str, int] = {}
    timestamp = 6

    def count(name: str) -> None:
        action_counts[name] = int(action_counts.get(name, 0)) + 1

    for _ in range(steps):
        timestamp += 1
        action = rng.choice(
            (
                "token_transfer",
                "perps_deposit",
                "perps_withdraw",
                "zusd_sp_deposit",
                "zusd_sp_withdraw",
                "cross_stream_atomic_reject",
                "zusd_replay_reject",
            )
        )
        balances = model["balances"]
        perps_collateral = model["perps_collateral"]
        sp_deposits = model["sp_deposits"]

        if action == "token_transfer":
            sender, receiver = (ALICE, BOB) if rng.randrange(2) == 0 else (BOB, ALICE)
            if int(balances[sender]) <= 0:
                continue
            amount = rng.randint(1, min(17, int(balances[sender])))
            nonce = int(model["token_nonce"][sender]) + 1
            app = _expect_ok(
                app,
                operations={"9": [_token_transfer(sender=sender, receiver=receiver, amount=amount, nonce=nonce)]},
                sender=sender,
                block_timestamp=timestamp,
                chain_balances={ALICE: 0},
            )
            model["token_nonce"][sender] = nonce
            balances[sender] -= amount
            balances[receiver] += amount
            accepted += 1
            count(action)

        elif action == "perps_deposit":
            actor = rng.choice(PARTICIPANTS)
            if int(balances[actor]) <= 0:
                continue
            amount = rng.randint(1, min(23, int(balances[actor])))
            app = _expect_ok(
                app,
                operations={
                    "8": [_perp_collateral_op(market_id=market_id, action="deposit_collateral", account=actor, amount=amount)]
                },
                sender=actor,
                block_timestamp=timestamp,
                chain_balances={ALICE: 0},
            )
            balances[actor] -= amount
            perps_collateral[actor] += amount
            accepted += 1
            count(action)

        elif action == "perps_withdraw":
            actor = rng.choice(PARTICIPANTS)
            if int(perps_collateral[actor]) <= 0:
                continue
            amount = rng.randint(1, min(11, int(perps_collateral[actor])))
            app = _expect_ok(
                app,
                operations={
                    "8": [_perp_collateral_op(market_id=market_id, action="withdraw_collateral", account=actor, amount=amount)]
                },
                sender=actor,
                block_timestamp=timestamp,
                chain_balances={ALICE: 0},
            )
            balances[actor] += amount
            perps_collateral[actor] -= amount
            accepted += 1
            count(action)

        elif action == "zusd_sp_deposit":
            actor = rng.choice(PARTICIPANTS)
            if int(balances[actor]) <= 0:
                continue
            amount = rng.randint(1, min(19, int(balances[actor])))
            nonce = int(model["zusd_nonce"][actor]) + 1
            app = _expect_ok(
                app,
                operations={"11": [_zusd_sp_op(action="deposit_sp", account=actor, amount=amount, nonce=nonce)]},
                sender=actor,
                block_timestamp=timestamp,
                chain_balances={ALICE: 0},
            )
            model["zusd_nonce"][actor] = nonce
            balances[actor] -= amount
            sp_deposits[actor] += amount
            accepted += 1
            count(action)

        elif action == "zusd_sp_withdraw":
            actor = rng.choice(PARTICIPANTS)
            if int(sp_deposits[actor]) <= 0:
                continue
            amount = rng.randint(1, min(13, int(sp_deposits[actor])))
            nonce = int(model["zusd_nonce"][actor]) + 1
            app = _expect_ok(
                app,
                operations={"11": [_zusd_sp_op(action="withdraw_sp", account=actor, amount=amount, nonce=nonce)]},
                sender=actor,
                block_timestamp=timestamp,
                chain_balances={ALICE: 0},
            )
            model["zusd_nonce"][actor] = nonce
            balances[actor] += amount
            sp_deposits[actor] -= amount
            accepted += 1
            count(action)

        elif action == "cross_stream_atomic_reject":
            actor = ALICE if int(balances[ALICE]) > 0 else BOB
            receiver = BOB if actor == ALICE else ALICE
            nonce = int(model["token_nonce"][actor]) + 1
            err = _expect_reject_unchanged(
                app,
                operations={
                    "9": [_token_transfer(sender=actor, receiver=receiver, amount=1, nonce=nonce)],
                    "8": [
                        _perp_collateral_op(
                            market_id=market_id,
                            action="deposit_collateral",
                            account=actor,
                            amount=1_000_000,
                        )
                    ],
                },
                sender=actor,
                block_timestamp=timestamp,
                expected_error_fragment="insufficient balance",
                chain_balances={ALICE: 0},
            )
            if "insufficient balance" not in err:
                raise AssertionError(err)
            rejected += 1
            count(action)

        elif action == "zusd_replay_reject":
            replay_candidates = [pk for pk in PARTICIPANTS if int(model["zusd_nonce"][pk]) > 0]
            actor = rng.choice(replay_candidates)
            replay_nonce = int(model["zusd_nonce"][actor])
            err = _expect_reject_unchanged(
                app,
                operations={"11": [_zusd_sp_op(action="deposit_sp", account=actor, amount=1, nonce=replay_nonce)]},
                sender=actor,
                block_timestamp=timestamp,
                expected_error_fragment="nonce invalid",
                chain_balances={ALICE: 0},
            )
            if "nonce invalid" not in err:
                raise AssertionError(err)
            rejected += 1
            count(action)

        _assert_fuzz_state(app, model, market_id=market_id)

    if accepted == 0 or rejected == 0:
        raise AssertionError("fuzz seed did not exercise both accepted and rejected actions")
    return {
        "seed": seed,
        "steps": steps,
        "accepted": accepted,
        "rejected": rejected,
        "action_counts": dict(sorted(action_counts.items())),
        "final_balances": {
            "alice": int(model["balances"][ALICE]),
            "bob": int(model["balances"][BOB]),
            "alice_perps_collateral": int(model["perps_collateral"][ALICE]),
            "bob_perps_collateral": int(model["perps_collateral"][BOB]),
            "alice_sp_deposit": int(model["sp_deposits"][ALICE]),
            "bob_sp_deposit": int(model["sp_deposits"][BOB]),
        },
    }


def run_fuzz_campaign(*, seeds: int = 4, steps: int = 32) -> dict[str, Any]:
    seed_receipts: list[dict[str, Any]] = []
    errors: list[str] = []
    with _patched_env(_base_env()):
        for seed in range(seeds):
            try:
                seed_receipts.append(_run_fuzz_seed(seed=seed, steps=steps))
            except Exception as exc:
                errors.append(f"seed {seed}: {exc}")
    return {
        "ok": not errors,
        "seed_count": seeds,
        "steps_per_seed": steps,
        "accepted_total": sum(int(item["accepted"]) for item in seed_receipts),
        "rejected_total": sum(int(item["rejected"]) for item in seed_receipts),
        "disaster_states": [
            "long_horizon_balance_drift",
            "long_horizon_cross_stream_partial_mutation",
            "long_horizon_nonce_replay_materializes",
        ],
        "seeds": seed_receipts,
        "errors": errors,
    }


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
    fuzz = run_fuzz_campaign()
    return {
        "schema": SCHEMA,
        "ok": accepted == len(scenarios) and bool(fuzz["ok"]),
        "chain_id": CHAIN_ID,
        "surface": (
            "stream11_zusd_monetary__stream9_zusd_token__stream8_clearinghouse_perps__"
            "autotrader_execute_once__confidential_live_admission__confidential_runtime_execute"
        ),
        "scenario_count": len(scenarios),
        "accepted_scenario_count": accepted,
        "disaster_states": [scenario["disaster_state"] for scenario in scenarios],
        "scenarios": scenarios,
        "fuzz_campaign": fuzz,
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
