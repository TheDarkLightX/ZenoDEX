from __future__ import annotations

from src.core.dex import DexState
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.state.balances import BalanceTable
from src.state.lp import LPTable


_CHAIN_ID = "tau-signed-surface"
_BLOCK_TIMESTAMP = 1
_DEADLINE = 10_000

_ALICE_SK = 21
_BOB_SK = 22
_CAROL_SK = 23
_ORACLE_SK = 24

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


def _apply_result(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]]) -> object:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(chain_id=_CHAIN_ID, oracle_pubkey=_ORACLE_PUBKEY)
    return apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=_BLOCK_TIMESTAMP,
    )


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]]) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, ops=ops)
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _sign(op: dict[str, object], *, signer_privkey: int, signer_pubkey: str, nonce: int) -> str:
    return sign_perp_op_for_engine(
        op,
        privkey=signer_privkey,
        chain_id=_CHAIN_ID,
        signer_pubkey=signer_pubkey,
        nonce=nonce,
    )


def _signed_init_market_2p(*, market_id: str, quote_asset: str, nonce_a: int, nonce_b: int) -> dict[str, object]:
    base = _op(
        market_id,
        "init_market_2p",
        version="1.0",
        quote_asset=quote_asset,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        deadline=_DEADLINE,
        nonce_a=int(nonce_a),
        nonce_b=int(nonce_b),
    )
    base["sig_a"] = _sign(base, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=nonce_a)
    base["sig_b"] = _sign(base, signer_privkey=_BOB_SK, signer_pubkey=_BOB_PUBKEY, nonce=nonce_b)
    return base


def test_init_market_2p_rejects_unknown_fields_before_signature_verification() -> None:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    relayer = "ff" * 48
    op = _signed_init_market_2p(market_id="perp:ch2p:surface-extra", quote_asset="0x" + "11" * 32, nonce_a=1, nonce_b=1)
    op["unexpected"] = 7

    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])

    assert res.ok is False
    assert res.error == "init_market_2p has unknown fields"


def test_init_market_2p_rejects_canonical_equivalent_duplicate_accounts() -> None:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    relayer = "ff" * 48
    op = _op(
        "perp:ch2p:surface-dup",
        "init_market_2p",
        version="1.0",
        quote_asset="0x" + "22" * 32,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey="0X" + _ALICE_PUBKEY,
        deadline=_DEADLINE,
        nonce_a=1,
        nonce_b=1,
    )
    op["sig_a"] = _sign(op, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=1)
    op["sig_b"] = _sign(op, signer_privkey=_ALICE_SK, signer_pubkey="0X" + _ALICE_PUBKEY, nonce=1)

    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])

    assert res.ok is False
    assert res.error == "accounts must be distinct"


def test_set_position_pair_rejects_market_account_mismatch_before_signature_verification() -> None:
    market_id = "perp:ch2p:surface-mismatch"
    quote_asset = "0x" + "33" * 32
    relayer = "ff" * 48
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1)],
    )

    op = _op(
        market_id,
        "set_position_pair",
        version="1.0",
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_CAROL_PUBKEY,
        new_position_base_a=5,
        new_position_base_b=-5,
        deadline=_DEADLINE,
        nonce_a=2,
        nonce_b=1,
    )
    op["sig_a"] = _sign(op, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=2)
    op["sig_b"] = _sign(op, signer_privkey=_CAROL_SK, signer_pubkey=_CAROL_PUBKEY, nonce=1)

    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])

    assert res.ok is False
    assert res.error == "accounts do not match this market"


def test_publish_clearing_price_rejects_non_positive_price_before_signature_verification() -> None:
    market_id = "perp:ch2p:surface-price"
    quote_asset = "0x" + "44" * 32
    relayer = "ff" * 48
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1)],
    )

    op = _op(
        market_id,
        "publish_clearing_price",
        version="1.0",
        price_e8=0,
        deadline=_DEADLINE,
        oracle_nonce=1,
        oracle_sig="0x" + "00" * 96,
    )
    res = _apply_result(state=state, tx_sender_pubkey=relayer, ops=[op])

    assert res.ok is False
    assert res.error == "publish_clearing_price requires price_e8 > 0"
