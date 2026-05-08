from __future__ import annotations

from dataclasses import replace
from typing import Any

from src.core.dex import DexState
from src.core.perps import PerpClearinghouse3pTransferMarketState
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.state.balances import BalanceTable
from src.state.lp import LPTable


_CHAIN_ID = "tau-test"
_BLOCK_TIMESTAMP = 1
_DEADLINE = 10_000

_ALICE_SK = 1
_BOB_SK = 2
_CAROL_SK = 3
_ORACLE_SK = 4

_ALICE_PUBKEY = bls_pubkey_hex_from_privkey(_ALICE_SK)
_BOB_PUBKEY = bls_pubkey_hex_from_privkey(_BOB_SK)
_CAROL_PUBKEY = bls_pubkey_hex_from_privkey(_CAROL_SK)
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
    oracle_adapter_bridge_verifier: Any = None,
    require_oracle_adapter_for_clearinghouse_settle_epoch: bool = False,
):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(
        chain_id=_CHAIN_ID,
        oracle_pubkey=_ORACLE_PUBKEY,
        operator_pubkey=operator_pubkey,
        oracle_adapter_bridge_verifier=oracle_adapter_bridge_verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=require_oracle_adapter_for_clearinghouse_settle_epoch,
    )
    return apply_perp_ops(
        config=cfg,
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
    oracle_adapter_bridge_verifier: Any = None,
    require_oracle_adapter_for_clearinghouse_settle_epoch: bool = False,
) -> DexState:
    res = _apply_result(
        state=state,
        tx_sender_pubkey=tx_sender_pubkey,
        ops=ops,
        block_timestamp=block_timestamp,
        operator_pubkey=operator_pubkey,
        oracle_adapter_bridge_verifier=oracle_adapter_bridge_verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=require_oracle_adapter_for_clearinghouse_settle_epoch,
    )
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _sign(op: dict[str, object], *, signer_privkey: int, signer_pubkey: str, nonce: int) -> str:
    return sign_perp_op_for_engine(op, privkey=signer_privkey, chain_id=_CHAIN_ID, signer_pubkey=signer_pubkey, nonce=nonce)


def _signed_init_market_3p(*, market_id: str, quote_asset: str, nonce_a: int, nonce_b: int, nonce_c: int, deadline: int) -> dict[str, object]:
    base = _op(
        market_id,
        "init_market_3p",
        version="1.1",
        quote_asset=quote_asset,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        account_c_pubkey=_CAROL_PUBKEY,
        deadline=int(deadline),
        nonce_a=int(nonce_a),
        nonce_b=int(nonce_b),
        nonce_c=int(nonce_c),
    )
    base["sig_a"] = _sign(base, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=nonce_a)
    base["sig_b"] = _sign(base, signer_privkey=_BOB_SK, signer_pubkey=_BOB_PUBKEY, nonce=nonce_b)
    base["sig_c"] = _sign(base, signer_privkey=_CAROL_SK, signer_pubkey=_CAROL_PUBKEY, nonce=nonce_c)
    return base


def _signed_set_position_triplet(
    *,
    market_id: str,
    new_a: int,
    new_b: int,
    new_c: int,
    nonce_a: int,
    nonce_b: int,
    nonce_c: int,
    deadline: int,
) -> dict[str, object]:
    base = _op(
        market_id,
        "set_position_triplet",
        version="1.1",
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        account_c_pubkey=_CAROL_PUBKEY,
        new_position_base_a=int(new_a),
        new_position_base_b=int(new_b),
        new_position_base_c=int(new_c),
        deadline=int(deadline),
        nonce_a=int(nonce_a),
        nonce_b=int(nonce_b),
        nonce_c=int(nonce_c),
    )
    base["sig_a"] = _sign(base, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=nonce_a)
    base["sig_b"] = _sign(base, signer_privkey=_BOB_SK, signer_pubkey=_BOB_PUBKEY, nonce=nonce_b)
    base["sig_c"] = _sign(base, signer_privkey=_CAROL_SK, signer_pubkey=_CAROL_PUBKEY, nonce=nonce_c)
    return base


def _signed_publish_price(*, market_id: str, price_e8: int, oracle_nonce: int, deadline: int) -> dict[str, object]:
    base = _op(
        market_id,
        "publish_clearing_price",
        version="1.1",
        price_e8=int(price_e8),
        deadline=int(deadline),
        oracle_nonce=int(oracle_nonce),
    )
    base["oracle_sig"] = _sign(base, signer_privkey=_ORACLE_SK, signer_pubkey=_ORACLE_PUBKEY, nonce=oracle_nonce)
    return base


def _settle_ready_state_3p(*, market_id: str, quote_asset: str, relayer: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[
            _signed_init_market_3p(
                market_id=market_id,
                quote_asset=quote_asset,
                nonce_a=1,
                nonce_b=1,
                nonce_c=1,
                deadline=_DEADLINE,
            )
        ],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_op(market_id, "advance_epoch", version="1.1", delta=1)],
    )
    return _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=100_000_000, oracle_nonce=1, deadline=_DEADLINE)],
    )


def _open_position_state_3p(*, market_id: str, quote_asset: str, relayer: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_3p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, nonce_c=1, deadline=_DEADLINE)],
    )

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse3pTransferMarketState)
    open_market = PerpClearinghouse3pTransferMarketState(
        quote_asset=m.quote_asset,
        account_a_pubkey=m.account_a_pubkey,
        account_b_pubkey=m.account_b_pubkey,
        account_c_pubkey=m.account_c_pubkey,
        state={**m.state, "position_base_a": 1_000, "position_base_b": -1_000, "position_base_c": 0},
    )
    markets = dict(state.perps.markets)
    markets[market_id] = open_market
    return replace(state, perps=replace(state.perps, markets=markets))


def test_init_market_3p_is_strict_about_prefix_and_signatures() -> None:
    quote_asset = "0x" + "33" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    bad_market_id = "perp:demo"
    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[
            _op(
                bad_market_id,
                "init_market_3p",
                version="1.1",
                quote_asset=quote_asset,
                account_a_pubkey=_ALICE_PUBKEY,
                account_b_pubkey=_BOB_PUBKEY,
                account_c_pubkey=_CAROL_PUBKEY,
            )
        ],
    )
    assert not res.ok
    assert res.error is not None and "perp:ch3p:" in res.error

    market_id = "perp:ch3p:demo"
    op = _signed_init_market_3p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, nonce_c=1, deadline=_DEADLINE)
    op_bad = dict(op)
    op_bad["sig_c"] = "0x" + "00" * 96
    res2 = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op_bad])
    assert not res2.ok
    assert res2.error is not None and res2.error.startswith("account_c signature invalid:")

    res3 = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])
    assert res3.ok is True, res3.error


def test_advance_epoch_3p_rejects_delta_gt_1() -> None:
    market_id = "perp:ch3p:epoch_delta"
    quote_asset = "0x" + "77" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[
            _signed_init_market_3p(
                market_id=market_id,
                quote_asset=quote_asset,
                nonce_a=1,
                nonce_b=1,
                nonce_c=1,
                deadline=_DEADLINE,
            )
        ],
    )

    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.1", delta=2)])
    assert not res.ok
    assert res.error == "advance_epoch delta must be 1 for clearinghouse markets"


def test_init_market_3p_rejects_expired_deadline() -> None:
    market_id = "perp:ch3p:expired"
    quote_asset = "0x" + "88" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    op = _signed_init_market_3p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, nonce_c=1, deadline=0)
    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op], block_timestamp=1)
    assert not res.ok
    assert res.error == "account_a signature invalid: signature expired (deadline)"


def test_init_market_3p_rejects_wrong_chain_id_signature() -> None:
    market_id = "perp:ch3p:chain_id"
    quote_asset = "0x" + "99" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    op = _op(
        market_id,
        "init_market_3p",
        version="1.1",
        quote_asset=quote_asset,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        account_c_pubkey=_CAROL_PUBKEY,
        deadline=_DEADLINE,
        nonce_a=1,
        nonce_b=1,
        nonce_c=1,
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
    op["sig_c"] = sign_perp_op_for_engine(
        op,
        privkey=_CAROL_SK,
        chain_id="tau-wrong",
        signer_pubkey=_CAROL_PUBKEY,
        nonce=1,
    )
    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])
    assert not res.ok
    assert res.error == "account_a signature invalid: invalid signature"


def test_publish_price_3p_rejects_zero_price() -> None:
    market_id = "perp:ch3p:zero_price"
    quote_asset = "0x" + "21" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_3p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, nonce_c=1, deadline=_DEADLINE)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_op(market_id, "advance_epoch", version="1.1", delta=1)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_publish_price(market_id=market_id, price_e8=0, oracle_nonce=1, deadline=_DEADLINE)],
    )
    assert not res.ok
    assert res.error == "publish_clearing_price requires price_e8 > 0"


def test_set_position_triplet_requires_net_zero_and_one_idle() -> None:
    market_id = "perp:ch3p:netzero"
    quote_asset = "0x" + "44" * 32
    relayer = "ff" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_3p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, nonce_c=1, deadline=_DEADLINE)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[
            _op(
                market_id,
                "set_position_triplet",
                version="1.1",
                account_a_pubkey=_ALICE_PUBKEY,
                account_b_pubkey=_BOB_PUBKEY,
                account_c_pubkey=_CAROL_PUBKEY,
                new_position_base_a=1,
                new_position_base_b=0,
                new_position_base_c=0,
                deadline=_DEADLINE,
                nonce_a=2,
                sig_a="0x" + "11" * 96,
                nonce_b=2,
                sig_b="0x" + "22" * 96,
                nonce_c=2,
                sig_c="0x" + "33" * 96,
            )
        ],
    )
    assert not res.ok
    assert res.error == "clearinghouse_3p requires net position == 0"

    res2 = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[
            _op(
                market_id,
                "set_position_triplet",
                version="1.1",
                account_a_pubkey=_ALICE_PUBKEY,
                account_b_pubkey=_BOB_PUBKEY,
                account_c_pubkey=_CAROL_PUBKEY,
                new_position_base_a=1,
                new_position_base_b=-2,
                new_position_base_c=1,
                deadline=_DEADLINE,
                nonce_a=2,
                sig_a="0x" + "11" * 96,
                nonce_b=2,
                sig_b="0x" + "22" * 96,
                nonce_c=2,
                sig_c="0x" + "33" * 96,
            )
        ],
    )
    assert not res2.ok
    assert res2.error == "clearinghouse_3p requires at least one flat position"


def test_settle_epoch_3p_can_transfer_distressed_side_and_preserve_conservation() -> None:
    market_id = "perp:ch3p:transfer"
    quote_asset = "0x" + "55" * 32
    relayer = "ff" * 48

    funded = BalanceTable()
    funded.set(_ALICE_PUBKEY, quote_asset, 1000)
    funded.set(_BOB_PUBKEY, quote_asset, 1000)
    funded.set(_CAROL_PUBKEY, quote_asset, 1000)
    state = DexState(balances=funded, pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_3p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, nonce_c=1, deadline=_DEADLINE)],
    )

    # Epoch 1: initialize index price at 1.00.
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.1", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_signed_publish_price(market_id=market_id, price_e8=100_000_000, oracle_nonce=1, deadline=_DEADLINE)])
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "settle_epoch", version="1.1")])

    # Fund all accounts (quote units; kernel stores quote-e8).
    state = _apply(
        state=state,
        tx_sender_pubkey=_ALICE_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.1", account_pubkey=_ALICE_PUBKEY, amount=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=_BOB_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.1", account_pubkey=_BOB_PUBKEY, amount=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=_CAROL_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.1", account_pubkey=_CAROL_PUBKEY, amount=200)],
    )

    # Open a matched AB position pair (C idle).
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_set_position_triplet(market_id=market_id, new_a=1000, new_b=-1000, new_c=0, nonce_a=2, nonce_b=2, nonce_c=2, deadline=_DEADLINE)],
    )

    # Epoch 2: +5% move triggers maintenance breach for the short; its position is transferred to idle C.
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "advance_epoch", version="1.1", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_signed_publish_price(market_id=market_id, price_e8=105_000_000, oracle_nonce=2, deadline=_DEADLINE)])
    state = _apply(state=state, tx_sender_pubkey=relayer, ops=[_op(market_id, "settle_epoch", version="1.1")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse3pTransferMarketState)

    assert int(m.state["position_base_a"]) == 1000
    assert int(m.state["position_base_b"]) == 0
    assert int(m.state["position_base_c"]) == -1000
    assert int(m.state["collateral_e8_a"]) == 15_000_000_000
    assert int(m.state["collateral_e8_b"]) == 4_475_000_000
    assert int(m.state["collateral_e8_c"]) == 20_000_000_000
    assert int(m.state["fee_pool_e8"]) == 525_000_000
    assert (
        int(m.state["collateral_e8_a"])
        + int(m.state["collateral_e8_b"])
        + int(m.state["collateral_e8_c"])
        + int(m.state["fee_pool_e8"])
        == int(m.state["net_deposited_e8"])
    )


def test_settle_epoch_3p_oracle_adapter_bridge_is_required_when_configured() -> None:
    market_id = "perp:ch3p:oracle_bridge_required"
    quote_asset = "0x" + "5a" * 32
    relayer = "ff" * 48
    state = _settle_ready_state_3p(market_id=market_id, quote_asset=quote_asset, relayer=relayer)

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_op(market_id, "settle_epoch", version="1.1")],
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
    )
    assert res.ok is False
    assert res.error == "settle_epoch requires oracle_adapter_bridge"


def test_settle_epoch_3p_oracle_adapter_bridge_binds_runtime_action_id() -> None:
    from src.integration.perp_engine import (
        _ORACLE_PERPS_INDEX_QUERY_ID,
        _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        PerpEngineConfig,
        _perps_clearinghouse_runtime_oracle_action_id,
    )

    market_id = "perp:ch3p:oracle_bridge_bound"
    quote_asset = "0x" + "5b" * 32
    relayer = "ff" * 48
    state = _settle_ready_state_3p(market_id=market_id, quote_asset=quote_asset, relayer=relayer)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert isinstance(market, PerpClearinghouse3pTransferMarketState)

    res_wrong = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_op(market_id, "settle_epoch", version="1.1", oracle_adapter_bridge={"schema": "test"})],
        oracle_adapter_bridge_verifier=lambda _bridge: {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": "sha256:" + "00" * 32,
        },
    )
    assert res_wrong.ok is False
    assert res_wrong.error == "oracle_adapter_bridge action_id mismatch"

    expected_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        PerpEngineConfig(chain_id=_CHAIN_ID),
        market_id=market_id,
        action_kind="settle_epoch",
        market_kind="clearinghouse_3p_transfer_v1",
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=(
            market.account_a_pubkey,
            market.account_b_pubkey,
            market.account_c_pubkey,
        ),
    )
    seen_bridge: dict[str, object] = {}

    def verifier(bridge: object) -> dict[str, object]:
        assert isinstance(bridge, dict)
        seen_bridge.update(bridge)
        return {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": expected_action_id,
        }

    res = _apply_result(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_op(market_id, "settle_epoch", version="1.1", oracle_adapter_bridge={"schema": "test"})],
        oracle_adapter_bridge_verifier=verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
    )
    assert res.ok is True, res.error
    assert seen_bridge == {"schema": "test"}


def test_set_market_params_3p_rejects_penalty_increase_with_open_positions() -> None:
    market_id = "perp:ch3p:params_open_pos_guard"
    quote_asset = "0x" + "66" * 32
    relayer = "ff" * 48

    state = _open_position_state_3p(market_id=market_id, quote_asset=quote_asset, relayer=relayer)

    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse3pTransferMarketState)
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
                version="1.1",
                params={"liquidation_penalty_bps": new_penalty},
            )
        ],
    )
    assert not res.ok
    assert res.error is not None and "cannot increase liquidation_penalty_bps while positions are open" in res.error


def test_set_market_params_3p_rejects_oracle_risk_loosenings_with_open_positions() -> None:
    market_id = "perp:ch3p:params_open_oracle_risk_guard"
    quote_asset = "0x" + "67" * 32
    relayer = "ff" * 48

    state = _open_position_state_3p(market_id=market_id, quote_asset=quote_asset, relayer=relayer)
    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse3pTransferMarketState)

    for params, expected_error in [
        (
            {"max_oracle_move_bps": int(m.state["max_oracle_move_bps"]) + 1},
            "cannot increase max_oracle_move_bps while positions are open",
        ),
        (
            {"max_oracle_staleness_epochs": int(m.state["max_oracle_staleness_epochs"]) + 1},
            "cannot increase max_oracle_staleness_epochs while positions are open",
        ),
    ]:
        res = _apply_result(
            state=state,
            tx_sender_pubkey=relayer,
            operator_pubkey=relayer,
            ops=[_op(market_id, "set_market_params", version="1.1", params=params)],
        )

        assert not res.ok
        assert res.error is not None and expected_error in res.error
