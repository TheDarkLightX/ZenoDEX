from __future__ import annotations

import pytest

from src.core import perp_liquidation_tau_source_binding as tau_source_binding
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


def _apply_perp_ops(state: DexState, op: dict[str, object], *, tx_sender_pubkey: str = _ALICE):
    return perp_engine.apply_perp_ops(
        config=perp_engine.PerpEngineConfig(operator_pubkey=_ALICE),
        state=state,
        operations={perp_engine.PERP_OPS_KEY: [op]},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=1,
    )


def test_tau_source_binding_keeps_bls_optional_until_signing(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(tau_source_binding, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc.bls is required"):
        tau_source_binding.build_perp_liquidation_tau_source_root_authority_binding(
            market_id="btc-usd",
            action=tau_source_binding.PARTIAL_LIQUIDATE_ACTION,
            valid_from_epoch=1,
            valid_until_epoch=2,
            authority_hash="sha256:" + "11" * 32,
            authority_state_root_hash="sha256:" + "22" * 32,
            policy_hash="sha256:" + "33" * 32,
            signer_privkey=1,
        )


def _init_2p_state(monkeypatch: pytest.MonkeyPatch) -> DexState:
    monkeypatch.setattr(perp_engine, "_verify_perp_op_signature", lambda *_, **__: None)
    result = _apply_perp_ops(_empty_state(), _base_2p_init())
    assert result.ok is True, result.error
    assert result.state is not None
    return result.state


def _init_3p_state(monkeypatch: pytest.MonkeyPatch) -> DexState:
    monkeypatch.setattr(perp_engine, "_verify_perp_op_signature", lambda *_, **__: None)
    result = _apply_perp_ops(_empty_state(), _base_3p_init())
    assert result.ok is True, result.error
    assert result.state is not None
    return result.state


def test_2p_pubkey_domain_errors_remain_signer_attributed(monkeypatch: pytest.MonkeyPatch) -> None:
    real_hex_to_bytes = perp_engine._hex_to_bytes_allow_0x

    def reject_pubkey(value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        if name not in {"account_a_pubkey", "account_b_pubkey"}:
            return real_hex_to_bytes(value, name=name, expected_nbytes=expected_nbytes)
        assert expected_nbytes == 48
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
    real_hex_to_bytes = perp_engine._hex_to_bytes_allow_0x

    def broken_pubkey(value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        if name not in {"account_a_pubkey", "account_b_pubkey"}:
            return real_hex_to_bytes(value, name=name, expected_nbytes=expected_nbytes)
        assert expected_nbytes == 48
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


def test_2p_generated_step_helper_bugs_reach_internal_error(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _init_2p_state(monkeypatch)

    def broken_step(*args: object, **kwargs: object):
        raise RuntimeError("2p generated step bug")

    monkeypatch.setattr(perp_engine, "_ch2p_step", broken_step)

    result = _apply_perp_ops(
        state,
        {
            "module": perp_engine.PERP_OP_MODULE,
            "version": "1.0",
            "market_id": "perp:ch2p:btc-usd",
            "action": "advance_epoch",
            "delta": 1,
        },
    )

    assert result.ok is False
    assert result.error == "internal error: RuntimeError"


def test_3p_generated_step_helper_bugs_reach_internal_error(monkeypatch: pytest.MonkeyPatch) -> None:
    state = _init_3p_state(monkeypatch)

    def broken_step(*args: object, **kwargs: object):
        raise RuntimeError("3p generated step bug")

    monkeypatch.setattr(perp_engine, "_ch3p_step", broken_step)

    result = _apply_perp_ops(
        state,
        {
            "module": perp_engine.PERP_OP_MODULE,
            "version": "1.1",
            "market_id": "perp:ch3p:btc-usd",
            "action": "advance_epoch",
            "delta": 1,
        },
    )

    assert result.ok is False
    assert result.error == "internal error: RuntimeError"


def test_3p_pubkey_helper_bugs_reach_internal_error(monkeypatch: pytest.MonkeyPatch) -> None:
    real_hex_to_bytes = perp_engine._hex_to_bytes_allow_0x

    def broken_pubkey(value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        if name not in {"account_a_pubkey", "account_b_pubkey", "account_c_pubkey"}:
            return real_hex_to_bytes(value, name=name, expected_nbytes=expected_nbytes)
        assert expected_nbytes == 48
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


def test_2p_init_state_helper_bugs_reach_internal_error(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(perp_engine, "_verify_perp_op_signature", lambda *_, **__: None)

    def broken_init_state() -> dict[str, object]:
        raise RuntimeError("2p init state helper bug")

    monkeypatch.setattr(perp_engine, "_ch2p_init_state_dict", broken_init_state)

    result = perp_engine.apply_perp_ops(
        config=perp_engine.PerpEngineConfig(),
        state=_empty_state(),
        operations={perp_engine.PERP_OPS_KEY: [_base_2p_init()]},
        tx_sender_pubkey=_ALICE,
        block_timestamp=1,
    )

    assert result.ok is False
    assert result.error == "internal error: RuntimeError"


def test_3p_init_state_helper_bugs_reach_internal_error(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(perp_engine, "_verify_perp_op_signature", lambda *_, **__: None)

    def broken_init_state() -> dict[str, object]:
        raise RuntimeError("3p init state helper bug")

    monkeypatch.setattr(perp_engine, "_ch3p_init_state_dict", broken_init_state)

    result = perp_engine.apply_perp_ops(
        config=perp_engine.PerpEngineConfig(),
        state=_empty_state(),
        operations={perp_engine.PERP_OPS_KEY: [_base_3p_init()]},
        tx_sender_pubkey=_ALICE,
        block_timestamp=1,
    )

    assert result.ok is False
    assert result.error == "internal error: RuntimeError"
