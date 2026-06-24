from __future__ import annotations

import pytest

import src.core.perps as perps


VALID_PUBKEY = "0x" + ("a" * 96)


def test_pubkey_bytes_or_none_rejects_invalid_pubkey_shape() -> None:
    assert perps._pubkey_bytes48_or_none("0x1") is None
    assert perps._pubkey_bytes48_or_none("not-hex") is None


def test_pubkey_bytes_or_none_does_not_swallow_canonicalizer_bug(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken_canonicalizer(*_args: object, **_kwargs: object) -> str:
        raise RuntimeError("unexpected pubkey canonicalizer bug")

    monkeypatch.setattr(perps, "canonical_hex_fixed_allow_0x", broken_canonicalizer)
    with pytest.raises(RuntimeError, match="unexpected pubkey canonicalizer bug"):
        perps._pubkey_bytes48_or_none(VALID_PUBKEY)
