from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
from src.core.perps import PerpClearinghouse2pMarketState
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.state.balances import BalanceTable
from src.state.lp import LPTable


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


def _apply_result(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], block_timestamp: int = _BLOCK_TIMESTAMP):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(chain_id=_CHAIN_ID, oracle_pubkey=_ORACLE_PUBKEY)
    return apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=int(block_timestamp),
    )


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], block_timestamp: int = _BLOCK_TIMESTAMP) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, ops=ops, block_timestamp=block_timestamp)
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
