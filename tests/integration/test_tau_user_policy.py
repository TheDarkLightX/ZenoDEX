from __future__ import annotations

import sqlite3

import pytest

import src.integration.tau_user_policy as tau_user_policy
from src.integration.tau_user_policy import (
    build_tau_testnet_wallet_outbound_o5_rule,
    get_or_create_tau_string_numeric_id,
)


def test_build_tau_testnet_wallet_outbound_o5_rule() -> None:
    rule = build_tau_testnet_wallet_outbound_o5_rule(scoped_sender_id=7, max_outbound_amount=100)
    assert "o5[t] = { 1 }:bv" in rule
    assert "{ 7 }:bv" in rule
    assert "{ 100 }:bv" in rule


def test_build_tau_testnet_wallet_outbound_o5_rule_rejects_bad_inputs() -> None:
    with pytest.raises(TypeError, match="scoped_sender_id must be an int"):
        build_tau_testnet_wallet_outbound_o5_rule(
            scoped_sender_id=True,  # type: ignore[arg-type]
            max_outbound_amount=100,
        )
    with pytest.raises(ValueError, match="max_outbound_amount out of u32 range"):
        build_tau_testnet_wallet_outbound_o5_rule(
            scoped_sender_id=7,
            max_outbound_amount=0x1_0000_0000,
        )


def test_get_or_create_tau_string_numeric_id_roundtrips(tmp_path) -> None:
    db_path = tmp_path / "node.db"
    first = get_or_create_tau_string_numeric_id(db_path=db_path, text="abc")
    second = get_or_create_tau_string_numeric_id(db_path=db_path, text="abc")
    third = get_or_create_tau_string_numeric_id(db_path=db_path, text="xyz")
    assert first == second
    assert third != first
    with sqlite3.connect(db_path) as conn:
        row = conn.execute("SELECT COUNT(*) FROM tau_strings").fetchone()
    assert row == (2,)


def test_get_or_create_tau_string_numeric_id_rejects_bad_text(tmp_path) -> None:
    with pytest.raises(ValueError, match="text must be a non-empty string"):
        get_or_create_tau_string_numeric_id(db_path=tmp_path / "node.db", text=" ")


def test_get_or_create_tau_string_numeric_id_rejects_missing_lastrowid(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    class _SelectCursor:
        lastrowid = None

        def fetchone(self):
            return None

    class _InsertCursor:
        lastrowid = None

    class _Conn:
        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc, tb) -> bool:
            return False

        def execute(self, query: str, params=()):
            if "SELECT id FROM tau_strings" in query:
                return _SelectCursor()
            if "INSERT INTO tau_strings" in query:
                return _InsertCursor()
            return _SelectCursor()

        def commit(self) -> None:
            return None

    monkeypatch.setattr(tau_user_policy.sqlite3, "connect", lambda _path: _Conn())
    with pytest.raises(RuntimeError, match="sqlite did not return a row id"):
        get_or_create_tau_string_numeric_id(db_path=tmp_path / "node.db", text="abc")
