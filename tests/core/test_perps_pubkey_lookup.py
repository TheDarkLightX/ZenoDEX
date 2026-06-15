from __future__ import annotations

import pytest

import src.core.perps as perps
from src.core.perps import _pubkey_bytes48_or_none


def test_pubkey_bytes48_or_none_treats_invalid_pubkeys_as_absent() -> None:
    assert _pubkey_bytes48_or_none("0x" + "11" * 48) == bytes.fromhex("11" * 48)
    assert _pubkey_bytes48_or_none("not-hex") is None
    assert _pubkey_bytes48_or_none(123) is None  # type: ignore[arg-type]


def test_pubkey_bytes48_or_none_propagates_programmer_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_canonicalizer(*_args: object, **_kwargs: object) -> str:
        raise RuntimeError("canonicalizer bug")

    monkeypatch.setattr(perps, "canonical_hex_fixed_allow_0x", broken_canonicalizer)

    with pytest.raises(RuntimeError, match="canonicalizer bug"):
        _pubkey_bytes48_or_none("0x" + "11" * 48)
