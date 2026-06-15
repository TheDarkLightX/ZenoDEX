from __future__ import annotations

from typing import cast

import pytest

from src.integration import dex_engine
from src.state.intents import Intent, IntentKind


def test_pubkey_parser_domain_errors_still_return_none(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_hex(_value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        assert name == "pk"
        assert expected_nbytes == 48
        raise ValueError("bad hex")

    monkeypatch.setattr(dex_engine, "_hex_to_bytes_allow_0x", reject_hex)

    assert dex_engine._pubkey_bytes48_or_none("0x" + "11" * 48, name="pk") is None


def test_pubkey_parser_helper_bugs_propagate(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_hex(_value: str, *, name: str, expected_nbytes: int | None = None) -> bytes:
        assert name == "pk"
        assert expected_nbytes == 48
        raise RuntimeError("pubkey parser bug")

    monkeypatch.setattr(dex_engine, "_hex_to_bytes_allow_0x", broken_hex)

    with pytest.raises(RuntimeError, match="pubkey parser bug"):
        dex_engine._pubkey_bytes48_or_none("0x" + "11" * 48, name="pk")


def test_scoped_upba_batch_domain_field_errors_return_false() -> None:
    class BadFieldIntent:
        kind = IntentKind.SWAP_EXACT_IN

        def get_field(self, _name: str) -> object:
            raise ValueError("bad field")

    assert dex_engine._is_supported_uniform_batch_swap_family([cast(Intent, BadFieldIntent())]) is False


def test_scoped_upba_batch_helper_bugs_propagate() -> None:
    class BrokenFieldIntent:
        kind = IntentKind.SWAP_EXACT_IN

        def get_field(self, _name: str) -> object:
            raise RuntimeError("intent field helper bug")

    with pytest.raises(RuntimeError, match="intent field helper bug"):
        dex_engine._is_supported_uniform_batch_swap_family([cast(Intent, BrokenFieldIntent())])
