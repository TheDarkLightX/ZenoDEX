from __future__ import annotations

from dataclasses import replace
from typing import Mapping

from src.core.dex import DexState
from src.core.perps import PerpClearinghouse2pMarketState
from src.integration.perp_engine import (
    _ORACLE_PERPS_INDEX_QUERY_ID,
    _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    PerpEngineConfig,
    _perps_clearinghouse_settle_oracle_runtime_facts,
    apply_perp_ops,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tests.integration.oracle_authorization_test_helpers import authorization_bundle

_CHAIN_ID = "tau-test"
_BLOCK_TIMESTAMP = 1
_DEADLINE = 10_000

_ALICE_SK = 1
_BOB_SK = 2
_ORACLE_SK = 3

_ALICE_PUBKEY = bls_pubkey_hex_from_privkey(_ALICE_SK)
_BOB_PUBKEY = bls_pubkey_hex_from_privkey(_BOB_SK)
_ORACLE_PUBKEY = bls_pubkey_hex_from_privkey(_ORACLE_SK)


def _op(market_id: str, action: str, *, version: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": version,
        "market_id": market_id,
        "action": action,
    }
    op.update(kwargs)
    return op


def _apply_result(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    block_timestamp: int = _BLOCK_TIMESTAMP,
    operator_pubkey: str | None = None,
):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(chain_id=_CHAIN_ID, oracle_pubkey=_ORACLE_PUBKEY, operator_pubkey=operator_pubkey)
    return apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=int(block_timestamp),
    )


def _apply_result_with_config(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    config: PerpEngineConfig,
    block_timestamp: int = _BLOCK_TIMESTAMP,
):
    return apply_perp_ops(
        config=config,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=int(block_timestamp),
    )


def _apply(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    block_timestamp: int = _BLOCK_TIMESTAMP,
    operator_pubkey: str | None = None,
) -> DexState:
    effective_operator = tx_sender_pubkey if operator_pubkey is None else operator_pubkey
    res = _apply_result(
        state=state,
        tx_sender_pubkey=tx_sender_pubkey,
        ops=ops,
        block_timestamp=block_timestamp,
        operator_pubkey=effective_operator,
    )
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _sign(op: dict[str, object], *, signer_privkey: int, signer_pubkey: str, nonce: int) -> str:
    return sign_perp_op_for_engine(op, privkey=signer_privkey, chain_id=_CHAIN_ID, signer_pubkey=signer_pubkey, nonce=nonce)


def _signed_init_market_2p(*, market_id: str, quote_asset: str, nonce_a: int, nonce_b: int, deadline: int) -> dict[str, object]:
    base = _op(
        market_id,
        "init_market_2p",
        version="1.0",
        quote_asset=quote_asset,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        deadline=int(deadline),
        nonce_a=int(nonce_a),
        nonce_b=int(nonce_b),
    )
    base["sig_a"] = _sign(base, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=nonce_a)
    base["sig_b"] = _sign(base, signer_privkey=_BOB_SK, signer_pubkey=_BOB_PUBKEY, nonce=nonce_b)
    return base


def _signed_set_position_pair(*, market_id: str, new_a: int, new_b: int, nonce_a: int, nonce_b: int, deadline: int) -> dict[str, object]:
    base = _op(
        market_id,
        "set_position_pair",
        version="1.0",
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        new_position_base_a=int(new_a),
        new_position_base_b=int(new_b),
        deadline=int(deadline),
        nonce_a=int(nonce_a),
        nonce_b=int(nonce_b),
    )
    base["sig_a"] = _sign(base, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=nonce_a)
    base["sig_b"] = _sign(base, signer_privkey=_BOB_SK, signer_pubkey=_BOB_PUBKEY, nonce=nonce_b)
    return base


def _signed_publish_price(*, market_id: str, price_e8: int, oracle_nonce: int, deadline: int) -> dict[str, object]:
    base = _op(
        market_id,
        "publish_clearing_price",
        version="1.0",
        price_e8=int(price_e8),
        deadline=int(deadline),
        oracle_nonce=int(oracle_nonce),
    )
    base["oracle_sig"] = _sign(base, signer_privkey=_ORACLE_SK, signer_pubkey=_ORACLE_PUBKEY, nonce=oracle_nonce)
    return base


def _initialized_ch2p_state(*, market_id: str, quote_asset: str) -> DexState:
    return _apply(
        state=DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()),
        tx_sender_pubkey="ff" * 48,
        ops=[
            _signed_init_market_2p(
                market_id=market_id,
                quote_asset=quote_asset,
                nonce_a=1,
                nonce_b=1,
                deadline=_DEADLINE,
            )
        ],
    )


def test_ch2p_advance_epoch_rejects_outsider_as_exact_noop() -> None:
    market_id = "perp:ch2p:authority_advance"
    operator = "ee" * 48
    outsider = "ff" * 48
    state = _initialized_ch2p_state(market_id=market_id, quote_asset="0x" + "a1" * 32)

    result = _apply_result(
        state=state,
        tx_sender_pubkey=outsider,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)],
    )

    assert result.ok is False
    assert result.error == "operator only"
    assert result.state is None
    assert result.effects is None


def test_ch2p_settle_epoch_rejects_outsider_as_exact_noop() -> None:
    market_id = "perp:ch2p:authority_settle"
    operator = "ee" * 48
    outsider = "ff" * 48
    state = _initialized_ch2p_state(market_id=market_id, quote_asset="0x" + "a2" * 32)
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=outsider,
        operator_pubkey=operator,
        ops=[
            _signed_publish_price(
                market_id=market_id,
                price_e8=100_000_000,
                oracle_nonce=1,
                deadline=_DEADLINE,
            )
        ],
    )

    result = _apply_result(
        state=state,
        tx_sender_pubkey=outsider,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch", version="1.0")],
    )

    assert result.ok is False
    assert result.error == "operator only"
    assert result.state is None
    assert result.effects is None


def test_ch2p_clear_breaker_rejects_outsider_as_exact_noop() -> None:
    market_id = "perp:ch2p:authority_clear_breaker"
    operator = "ee" * 48
    outsider = "ff" * 48
    state = _initialized_ch2p_state(market_id=market_id, quote_asset="0x" + "a3" * 32)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert isinstance(market, PerpClearinghouse2pMarketState)
    breaker_market = PerpClearinghouse2pMarketState(
        quote_asset=market.quote_asset,
        account_a_pubkey=market.account_a_pubkey,
        account_b_pubkey=market.account_b_pubkey,
        state={
            **market.state,
            "breaker_active": True,
            "breaker_last_trigger_epoch": int(market.state["now_epoch"]),
        },
    )
    markets = dict(state.perps.markets)
    markets[market_id] = breaker_market
    state = replace(state, perps=replace(state.perps, markets=markets))

    result = _apply_result(
        state=state,
        tx_sender_pubkey=outsider,
        operator_pubkey=operator,
        ops=[_op(market_id, "clear_breaker", version="1.0")],
    )
    assert result.ok is False
    assert result.error == "operator only"
    assert result.state is None
    assert result.effects is None

    accepted = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "clear_breaker", version="1.0")],
    )
    assert accepted.ok is True, accepted.error
    assert accepted.state is not None and accepted.state.perps is not None
    accepted_market = accepted.state.perps.markets[market_id]
    assert isinstance(accepted_market, PerpClearinghouse2pMarketState)
    assert accepted_market.state["breaker_active"] is False


def _accepted_bridge_verifier(expected_action_id: str):
    def _verifier(bridge: object) -> dict[str, object]:
        result = {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": expected_action_id,
        }
        if isinstance(bridge, Mapping):
            result.update(dict(bridge.get("verified_result", {})))
        return result

    return _verifier


def _bridge_for_authorization(authorization: Mapping[str, object]) -> dict[str, object]:
    auth = authorization["authorization"]
    assert isinstance(auth, Mapping)
    return {
        "schema": "test",
        "verified_result": {
            "value_hash": auth["value_hash"],
            "observed_epoch": auth["observed_epoch"],
            "expires_at_epoch": auth["expires_at_epoch"],
            "feed_registry_root": auth["feed_registry_root"],
            "query_policy_root": auth["query_policy_root"],
            "source_registry_root": auth["source_registry_root"],
            "reporter_registry_root": auth["reporter_registry_root"],
            "receipt_graph_root": auth["receipt_graph_root"],
        },
    }


def _clearinghouse_authorization_for(
    runtime: dict[str, object],
    *,
    observed_epoch: int,
    value_e8: int | None = None,
) -> dict[str, object]:
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    query_id = str(runtime["query_id"])
    auth = {
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed_epoch),
        "confidence_e8": 10_000,
        "deviation_bps": 5,
        "observed_epoch": int(observed_epoch),
        "expires_at_epoch": int(runtime["now_epoch"]),
        "feed_id": "feed:perps:index",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "perps-clearinghouse"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "perps-clearinghouse"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "perps-clearinghouse"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "perps-clearinghouse"}),
        "evidence_class": "O3",
        "economic_envelope_id": "perps-clearinghouse-critical-envelope",
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "perps-clearinghouse"}),
    }
    return authorization_bundle(auth)


def _ready_ch2p_price_published_market() -> tuple[DexState, str, str]:
    market_id = "perp:ch2p:oracle-auth"
    quote_asset = "0x" + "91" * 32
    relayer = "ff" * 48
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=100_000_000, oracle_nonce=1, deadline=_DEADLINE)],
    )
    return state, market_id, relayer


def _clearinghouse_authorized_config(
    state: DexState,
    market_id: str,
    *,
    operator_pubkey: str,
) -> tuple[PerpEngineConfig, dict[str, object]]:
    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert isinstance(market, PerpClearinghouse2pMarketState)
    cfg = PerpEngineConfig(
        chain_id=_CHAIN_ID,
        oracle_pubkey=_ORACLE_PUBKEY,
        operator_pubkey=operator_pubkey,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
    )
    runtime = _perps_clearinghouse_settle_oracle_runtime_facts(
        cfg,
        market_id=market_id,
        market_kind="clearinghouse_2p_v1",
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
    )
    cfg = replace(cfg, oracle_adapter_bridge_verifier=_accepted_bridge_verifier(str(runtime["action_id"])))
    return cfg, runtime


def test_init_market_2p_is_strict_about_prefix_and_signatures() -> None:
    quote_asset = "0x" + "33" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # v0.2 market ids are namespaced (fail-closed so semantics don't mix by accident).
    bad_market_id = "perp:demo"
    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[
            _op(
                bad_market_id,
                "init_market_2p",
                version="1.0",
                quote_asset=quote_asset,
                account_a_pubkey=_ALICE_PUBKEY,
                account_b_pubkey=_BOB_PUBKEY,
            )
        ],
    )
    assert not res.ok
    assert res.error is not None and "perp:ch2p:" in res.error

    market_id = "perp:ch2p:demo"
    op = _signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)
    op_bad = dict(op)
    op_bad["sig_b"] = "0x" + "00" * 96
    res2 = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op_bad])
    assert not res2.ok
    assert res2.error is not None and res2.error.startswith("account_b signature invalid:")

    res3 = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])
    assert res3.ok is True, res3.error


def test_advance_epoch_2p_rejects_delta_gt_1() -> None:
    market_id = "perp:ch2p:epoch_delta"
    quote_asset = "0x" + "77" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        operator_pubkey=relayer,
        ops=[_op(market_id, "advance_epoch", version="1.0", delta=2)],
    )
    assert not res.ok
    assert res.error == "advance_epoch delta must be 1 for clearinghouse markets"


def test_init_market_2p_rejects_expired_deadline() -> None:
    market_id = "perp:ch2p:expired"
    quote_asset = "0x" + "88" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    op = _signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=0)
    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op], block_timestamp=1)
    assert not res.ok
    assert res.error == "account_a signature invalid: signature expired (deadline)"


def test_init_market_2p_rejects_missing_deadline_fail_closed() -> None:
    quote_asset = "0x" + "11" * 32
    relayer = "ff" * 48
    market_id = "perp:ch2p:missing_deadline"

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    op = _op(
        market_id,
        "init_market_2p",
        version="1.0",
        quote_asset=quote_asset,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        nonce_a=1,
        sig_a="0x" + "00" * 96,
        nonce_b=1,
        sig_b="0x" + "00" * 96,
        # deadline intentionally omitted
    )
    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])
    assert not res.ok
    assert res.error == "account_a signature invalid: deadline must be an int"


def test_init_market_2p_accepts_0X_prefix_for_hex_fields() -> None:
    quote_asset = "0x" + "22" * 32
    relayer = "ff" * 48
    market_id = "perp:ch2p:hex_prefix_0X"

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    op = _op(
        market_id,
        "init_market_2p",
        version="1.0",
        quote_asset=quote_asset,
        account_a_pubkey="0X" + _ALICE_PUBKEY,
        account_b_pubkey="0X" + _BOB_PUBKEY,
        deadline=_DEADLINE,
        nonce_a=1,
        nonce_b=1,
    )
    op["sig_a"] = _sign(op, signer_privkey=_ALICE_SK, signer_pubkey="0X" + _ALICE_PUBKEY, nonce=1).replace("0x", "0X", 1)
    op["sig_b"] = _sign(op, signer_privkey=_BOB_SK, signer_pubkey="0X" + _BOB_PUBKEY, nonce=1).replace("0x", "0X", 1)

    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])
    assert res.ok is True, res.error

def test_init_market_2p_rejects_wrong_chain_id_signature() -> None:
    market_id = "perp:ch2p:chain_id"
    quote_asset = "0x" + "99" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    op = _op(
        market_id,
        "init_market_2p",
        version="1.0",
        quote_asset=quote_asset,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        deadline=_DEADLINE,
        nonce_a=1,
        nonce_b=1,
    )
    op["sig_a"] = sign_perp_op_for_engine(
        op,
        privkey=_ALICE_SK,
        chain_id="tau-wrong",
        signer_pubkey=_ALICE_PUBKEY,
        nonce=1,
    )
    op["sig_b"] = sign_perp_op_for_engine(
        op,
        privkey=_BOB_SK,
        chain_id="tau-wrong",
        signer_pubkey=_BOB_PUBKEY,
        nonce=1,
    )
    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])
    assert not res.ok
    assert res.error == "account_a signature invalid: invalid signature"


def test_publish_price_2p_rejects_zero_price() -> None:
    market_id = "perp:ch2p:zero_price"
    quote_asset = "0x" + "12" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=0, oracle_nonce=1, deadline=_DEADLINE)],
    )
    assert not res.ok
    assert res.error == "publish_clearing_price requires price_e8 > 0"


def test_init_market_2p_rejects_nonce_replay_and_is_transaction_atomic() -> None:
    quote_asset = "0x" + "aa" * 32
    relayer = "ff" * 48

    state0 = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    op1 = _signed_init_market_2p(
        market_id="perp:ch2p:atomic1",
        quote_asset=quote_asset,
        nonce_a=1,
        nonce_b=1,
        deadline=_DEADLINE,
    )
    op2 = _signed_init_market_2p(
        market_id="perp:ch2p:atomic2",
        quote_asset=quote_asset,
        nonce_a=2,
        nonce_b=2,
        deadline=_DEADLINE,
    )
    op2_bad = dict(op2)
    op2_bad["sig_b"] = "0x" + "00" * 96

    # If any op fails, nothing commits (including nonce consumption from earlier ops).
    res = _apply_result(state=state0, tx_sender_pubkey=relayer, ops=[op1, op2_bad])
    assert not res.ok
    assert res.error is not None and res.error.startswith("account_b signature invalid:")

    res2 = _apply_result(state=state0, tx_sender_pubkey=relayer, ops=[op1])
    assert res2.ok is True, res2.error

    # Nonce replay is rejected after a successful commit.
    state1 = res2.state
    assert state1 is not None
    res3 = _apply_result(
        state=state1,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id="perp:ch2p:replay", quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )
    assert not res3.ok
    assert res3.error == "account_a signature invalid: nonce invalid"


def test_set_position_pair_requires_net_zero() -> None:
    market_id = "perp:ch2p:netzero"
    quote_asset = "0x" + "44" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[
            _op(
                market_id,
                "set_position_pair",
                version="1.0",
                account_a_pubkey=_ALICE_PUBKEY,
                account_b_pubkey=_BOB_PUBKEY,
                new_position_base_a=1,
                new_position_base_b=0,
                deadline=_DEADLINE,
                nonce_a=2,
                sig_a="0x" + "11" * 96,
                nonce_b=2,
                sig_b="0x" + "22" * 96,
            )
        ],
    )
    assert not res.ok
    assert res.error == "clearinghouse_2p requires net position == 0"


def test_settle_epoch_2p_preserves_exact_conservation_in_quote_e8() -> None:
    market_id = "perp:ch2p:dust"
    quote_asset = "0x" + "55" * 32
    relayer = "ff" * 48

    funded = BalanceTable()
    funded.set(_ALICE_PUBKEY, quote_asset, 10)
    funded.set(_BOB_PUBKEY, quote_asset, 10)
    state = DexState(balances=funded, pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )

    # Epoch 1: initialize index price at 1.00.
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=100_000_000, oracle_nonce=1, deadline=_DEADLINE)],
    )
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "settle_epoch", version="1.0")])

    # Minimal collateral so the initial-margin guard is satisfiable.
    state = _apply(
        state=state,
        tx_sender_pubkey=_ALICE_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=_ALICE_PUBKEY, amount=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=_BOB_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=_BOB_PUBKEY, amount=1)],
    )

    # Open a tiny matched pair position (net-zero, quote-e8 accounting).
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_set_position_pair(market_id=market_id, new_a=1, new_b=-1, nonce_a=2, nonce_b=2, deadline=_DEADLINE)],
    )

    # Epoch 2: a +1 tick move in price_e8 creates xs=[+1, -1] at settlement.
    # With quote-e8 collateral, this is exact and must conserve total deposits.
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=100_000_001, oracle_nonce=2, deadline=_DEADLINE)],
    )
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "settle_epoch", version="1.0")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse2pMarketState)
    assert m.account_a_pubkey == _ALICE_PUBKEY
    assert m.account_b_pubkey == _BOB_PUBKEY
    assert int(m.state["collateral_e8_a"]) + int(m.state["collateral_e8_b"]) + int(m.state["fee_pool_e8"]) == int(
        m.state["net_deposited_e8"]
    )


def test_settle_epoch_2p_requires_typed_oracle_authorization_when_configured() -> None:
    state, market_id, relayer = _ready_ch2p_price_published_market()
    cfg, _runtime = _clearinghouse_authorized_config(state, market_id, operator_pubkey=relayer)

    res = _apply_result_with_config(
        state=state,
        tx_sender_pubkey=relayer,
        config=cfg,
        ops=[
            _op(
                market_id,
                "settle_epoch",
                version="1.0",
                oracle_adapter_bridge={"schema": "test"},
            )
        ],
    )

    assert res.ok is False
    assert res.error == "clearinghouse_settle_oracle_authorization_required"


def test_settle_epoch_2p_accepts_matching_typed_oracle_authorization() -> None:
    state, market_id, relayer = _ready_ch2p_price_published_market()
    cfg, runtime = _clearinghouse_authorized_config(state, market_id, operator_pubkey=relayer)
    auth = _clearinghouse_authorization_for(runtime, observed_epoch=int(runtime["now_epoch"]))

    res = _apply_result_with_config(
        state=state,
        tx_sender_pubkey=relayer,
        config=cfg,
        ops=[
            _op(
                market_id,
                "settle_epoch",
                version="1.0",
                oracle_adapter_bridge=_bridge_for_authorization(auth),
                oracle_authorization=auth,
            )
        ],
    )

    assert res.ok is True, res.error


def test_settle_epoch_2p_rejects_typed_oracle_authorization_value_mismatch() -> None:
    state, market_id, relayer = _ready_ch2p_price_published_market()
    cfg, runtime = _clearinghouse_authorized_config(state, market_id, operator_pubkey=relayer)
    auth = _clearinghouse_authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        value_e8=int(runtime["runtime_value_e8"]) + 1,
    )

    res = _apply_result_with_config(
        state=state,
        tx_sender_pubkey=relayer,
        config=cfg,
        ops=[
            _op(
                market_id,
                "settle_epoch",
                version="1.0",
                oracle_adapter_bridge=_bridge_for_authorization(auth),
                oracle_authorization=auth,
            )
        ],
    )

    assert res.ok is False
    assert res.error is not None
    assert "runtime_value_e8 mismatch" in res.error


def test_settle_epoch_2p_rejects_oracle_authorization_unbound_from_bridge() -> None:
    state, market_id, relayer = _ready_ch2p_price_published_market()
    cfg, runtime = _clearinghouse_authorized_config(state, market_id, operator_pubkey=relayer)
    auth = _clearinghouse_authorization_for(runtime, observed_epoch=int(runtime["now_epoch"]))
    bridge = _bridge_for_authorization(auth)
    verified_result = bridge["verified_result"]
    assert isinstance(verified_result, dict)
    verified_result["value_hash"] = oracle_value_hash(
        query_id=str(runtime["query_id"]),
        value_e8=int(runtime["runtime_value_e8"]) + 1,
        observed_epoch=int(runtime["now_epoch"]),
    )

    res = _apply_result_with_config(
        state=state,
        tx_sender_pubkey=relayer,
        config=cfg,
        ops=[
            _op(
                market_id,
                "settle_epoch",
                version="1.0",
                oracle_adapter_bridge=bridge,
                oracle_authorization=auth,
            )
        ],
    )

    assert res.ok is False
    assert res.error is not None
    assert "oracle_adapter_bridge value_hash mismatch" in res.error


def test_settle_epoch_2p_pair_liquidation_closes_both_positions() -> None:
    market_id = "perp:ch2p:liq"
    quote_asset = "0x" + "66" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # Seed balances (collateral deposits draw from balances).
    funded = BalanceTable()
    funded.set(_ALICE_PUBKEY, quote_asset, 1000)
    funded.set(_BOB_PUBKEY, quote_asset, 1000)
    state = replace(state, balances=funded)

    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )

    # Epoch 1: establish index price.
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=100_000_000, oracle_nonce=1, deadline=_DEADLINE)],
    )
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "settle_epoch", version="1.0")])

    # Deposit collateral for both sides (user-authenticated).
    state = _apply(
        state=state,
        tx_sender_pubkey=_ALICE_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=_ALICE_PUBKEY, amount=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=_BOB_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=_BOB_PUBKEY, amount=100)],
    )

    # Open a matched pair position.
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_set_position_pair(market_id=market_id, new_a=1000, new_b=-1000, nonce_a=2, nonce_b=2, deadline=_DEADLINE)],
    )

    # Epoch 2: a +5% move makes the short side under maintenance; pair liquidation closes both positions.
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=105_000_000, oracle_nonce=2, deadline=_DEADLINE)],
    )
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "settle_epoch", version="1.0")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse2pMarketState)
    assert int(m.state["fee_pool_e8"]) == 525_000_000
    assert int(m.state["collateral_e8_a"]) == 15_000_000_000
    assert int(m.state["collateral_e8_b"]) == 4_475_000_000
    assert int(m.state["position_base_a"]) == 0
    assert int(m.state["position_base_b"]) == 0
    assert int(m.state["entry_price_e8_a"]) == 0
    assert int(m.state["entry_price_e8_b"]) == 0
    assert int(m.state["collateral_e8_a"]) + int(m.state["collateral_e8_b"]) + int(m.state["fee_pool_e8"]) == int(
        m.state["net_deposited_e8"]
    )


def test_set_market_params_2p_rejects_penalty_increase_with_open_positions() -> None:
    market_id = "perp:ch2p:params_open_pos_guard"
    quote_asset = "0x" + "42" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, deadline=_DEADLINE)],
    )

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse2pMarketState)
    open_market = PerpClearinghouse2pMarketState(
        quote_asset=m.quote_asset,
        account_a_pubkey=m.account_a_pubkey,
        account_b_pubkey=m.account_b_pubkey,
        state={**m.state, "position_base_a": 1_000, "position_base_b": -1_000},
    )
    markets = dict(state.perps.markets)
    markets[market_id] = open_market
    state = replace(state, perps=replace(state.perps, markets=markets))

    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse2pMarketState)
    old_penalty = int(m.state["liquidation_penalty_bps"])
    maint = int(m.state["maintenance_margin_bps"])
    new_penalty = old_penalty + 1
    assert new_penalty < maint

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        operator_pubkey=relayer,
        ops=[
            _op(
                market_id,
                "set_market_params",
                version="1.0",
                params={"liquidation_penalty_bps": new_penalty},
            )
        ],
    )
    assert not res.ok
    assert res.error is not None and "cannot increase liquidation_penalty_bps while positions are open" in res.error
