from __future__ import annotations

from src.core.dex import DexState
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_perp_op_for_engine
from src.state.balances import BalanceTable
from src.state.lp import LPTable


_CHAIN_ID = "tau-auth-guard"
_BLOCK_TIMESTAMP = 1
_DEADLINE = 10_000

_ALICE_SK = 11
_BOB_SK = 12
_CAROL_SK = 13
_ORACLE_SK = 14

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
    allow_isolated_markets: bool = False,
    operator_pubkey: str | None = None,
) -> object:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(
        chain_id=_CHAIN_ID,
        oracle_pubkey=_ORACLE_PUBKEY,
        allow_isolated_markets=allow_isolated_markets,
        operator_pubkey=operator_pubkey,
    )
    return apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=_BLOCK_TIMESTAMP,
    )


def _apply(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    allow_isolated_markets: bool = False,
    operator_pubkey: str | None = None,
) -> DexState:
    res = _apply_result(
        state=state,
        tx_sender_pubkey=tx_sender_pubkey,
        ops=ops,
        allow_isolated_markets=allow_isolated_markets,
        operator_pubkey=operator_pubkey,
    )
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


def _signed_init_market_3p(*, market_id: str, quote_asset: str, nonce_a: int, nonce_b: int, nonce_c: int) -> dict[str, object]:
    base = _op(
        market_id,
        "init_market_3p",
        version="1.1",
        quote_asset=quote_asset,
        account_a_pubkey=_ALICE_PUBKEY,
        account_b_pubkey=_BOB_PUBKEY,
        account_c_pubkey=_CAROL_PUBKEY,
        deadline=_DEADLINE,
        nonce_a=int(nonce_a),
        nonce_b=int(nonce_b),
        nonce_c=int(nonce_c),
    )
    base["sig_a"] = _sign(base, signer_privkey=_ALICE_SK, signer_pubkey=_ALICE_PUBKEY, nonce=nonce_a)
    base["sig_b"] = _sign(base, signer_privkey=_BOB_SK, signer_pubkey=_BOB_PUBKEY, nonce=nonce_b)
    base["sig_c"] = _sign(base, signer_privkey=_CAROL_SK, signer_pubkey=_CAROL_PUBKEY, nonce=nonce_c)
    return base


def test_isolated_deposit_collateral_accepts_canonical_equivalent_sender_hex() -> None:
    market_id = "perp:auth:isolated-0x"
    quote_asset = "0x" + "21" * 32
    operator = "aa" * 48

    balances = BalanceTable()
    balances.set(_ALICE_PUBKEY, quote_asset, 100)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        ops=[_op(market_id, "init_market", version="0.1", quote_asset=quote_asset)],
        allow_isolated_markets=True,
        operator_pubkey=operator,
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey="0X" + _ALICE_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="0.1", account_pubkey=_ALICE_PUBKEY, amount=10)],
        allow_isolated_markets=True,
    )
    assert res.ok is True, res.error


def test_ch2p_deposit_collateral_rejects_sender_mismatch() -> None:
    market_id = "perp:ch2p:auth-mismatch"
    quote_asset = "0x" + "22" * 32
    relayer = "ff" * 48

    balances = BalanceTable()
    balances.set(_ALICE_PUBKEY, quote_asset, 100)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_2p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=_BOB_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=_ALICE_PUBKEY, amount=10)],
    )
    assert res.ok is False
    assert res.error == "account_pubkey must match tx sender"


def test_ch3p_deposit_collateral_rejects_sender_mismatch() -> None:
    market_id = "perp:ch3p:auth-mismatch"
    quote_asset = "0x" + "23" * 32
    relayer = "ff" * 48

    balances = BalanceTable()
    balances.set(_ALICE_PUBKEY, quote_asset, 100)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=relayer,
        ops=[_signed_init_market_3p(market_id=market_id, quote_asset=quote_asset, nonce_a=1, nonce_b=1, nonce_c=1)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=_BOB_PUBKEY,
        ops=[_op(market_id, "deposit_collateral", version="1.1", account_pubkey=_ALICE_PUBKEY, amount=10)],
    )
    assert res.ok is False
    assert res.error == "account_pubkey must match tx sender"
