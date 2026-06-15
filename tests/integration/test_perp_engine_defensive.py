from __future__ import annotations

import pytest

from src.core.dex import DexState
from src.integration import perp_engine
from src.state.balances import BalanceTable
from src.state.lp import LPTable

_ALICE = "0x" + "11" * 48
_BOB = "0x" + "22" * 48
_CAROL = "0x" + "33" * 48


def _base_2p_init() -> dict[str, object]:
    return {
        "module": perp_engine.PERP_OP_MODULE,
        "version": "1.0",
        "market_id": "perp:ch2p:btc-usd",
        "action": "init_market_2p",
        "quote_asset": "zUSD",
        "account_a_pubkey": _ALICE,
        "account_b_pubkey": _BOB,
        "deadline": 1,
        "nonce_a": 1,
        "sig_a": "0x" + "aa" * 96,
        "nonce_b": 1,
        "sig_b": "0x" + "bb" * 96,
    }


def _base_3p_init() -> dict[str, object]:
    op = _base_2p_init()
    op.update(
        {
            "version": "1.1",
            "market_id": "perp:ch3p:btc-usd",
            "action": "init_market_3p",
            "account_c_pubkey": _CAROL,
            "nonce_c": 1,
            "sig_c": "0x" + "cc" * 96,
        }
    )
    return op


def _empty_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def test_2p_pubkey_domain_errors_remain_signer_attributed(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_pubkey(_value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        assert expected_nbytes == 48
        assert name in {"account_a_pubkey", "account_b_pubkey"}
        raise ValueError("bad pubkey")

    monkeypatch.setattr(perp_engine, "_hex_to_bytes_allow_0x", reject_pubkey)

    result = perp_engine.apply_perp_ops(
        config=perp_engine.PerpEngineConfig(),
        state=_empty_state(),
        operations={perp_engine.PERP_OPS_KEY: [_base_2p_init()]},
        tx_sender_pubkey=_ALICE,
        block_timestamp=1,
    )

    assert result.ok is False
    assert result.error is not None
    assert "signature" in result.error or "py_ecc" in result.error or "signer" in result.error


def test_2p_pubkey_helper_bugs_reach_internal_error(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_pubkey(_value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        assert expected_nbytes == 48
        assert name in {"account_a_pubkey", "account_b_pubkey"}
        raise RuntimeError("2p pubkey helper bug")

    monkeypatch.setattr(perp_engine, "_hex_to_bytes_allow_0x", broken_pubkey)

    result = perp_engine.apply_perp_ops(
        config=perp_engine.PerpEngineConfig(),
        state=_empty_state(),
        operations={perp_engine.PERP_OPS_KEY: [_base_2p_init()]},
        tx_sender_pubkey=_ALICE,
        block_timestamp=1,
    )

    assert result.ok is False
    assert result.error == "internal error: RuntimeError"


def test_3p_pubkey_helper_bugs_reach_internal_error(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_pubkey(_value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        assert expected_nbytes == 48
        assert name in {"account_a_pubkey", "account_b_pubkey", "account_c_pubkey"}
        raise RuntimeError("3p pubkey helper bug")

    monkeypatch.setattr(perp_engine, "_hex_to_bytes_allow_0x", broken_pubkey)

    result = perp_engine.apply_perp_ops(
        config=perp_engine.PerpEngineConfig(),
        state=_empty_state(),
        operations={perp_engine.PERP_OPS_KEY: [_base_3p_init()]},
        tx_sender_pubkey=_ALICE,
        block_timestamp=1,
    )

    assert result.ok is False
    assert result.error == "internal error: RuntimeError"
