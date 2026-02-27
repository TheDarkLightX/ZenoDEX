"""BVA tests for replay-protection nonces (`src/state/nonces.py`)."""

from __future__ import annotations

import pytest

from src.state.nonces import NonceTable


PK_48B = "0x" + "11" * 48


class TestNonceTableBVA:
    def test_get_last_default_zero(self) -> None:
        t = NonceTable()
        assert t.get_last(PK_48B) == 0

    def test_set_last_canonicalizes_pubkey(self) -> None:
        t = NonceTable()
        pk_raw_upper_no0x = ("AA" * 48)  # raw hex, uppercase, no 0x
        pk_canon = "0x" + ("aa" * 48)

        t.set_last(pk_raw_upper_no0x, 7)
        assert t.get_last(pk_canon) == 7

    @pytest.mark.parametrize(
        "last_nonce,expect_ok,reason",
        [
            (-1, False, "just below min=0"),
            (0, True, "at min"),
            (1, True, "just above min"),
            (0xFFFFFFFF - 1, True, "just below max u32"),
            (0xFFFFFFFF, True, "at max u32"),
            (0xFFFFFFFF + 1, False, "just above max u32"),
            (True, False, "bool is not an int nonce"),
        ],
    )
    def test_set_last_nonce_bounds(self, last_nonce: int, expect_ok: bool, reason: str) -> None:
        t = NonceTable()
        if expect_ok:
            t.set_last(PK_48B, last_nonce)
            assert t.get_last(PK_48B) == int(last_nonce)
        else:
            with pytest.raises((TypeError, ValueError), match="nonce|u32|int|non-negative|pubkey"):
                t.set_last(PK_48B, last_nonce)

    @pytest.mark.parametrize(
        "pubkey,reason",
        [
            ("", "empty"),
            ("0x", "just prefix"),
            ("0x" + "11" * 47, "just below 48 bytes"),
            ("0x" + "11" * 49, "just above 48 bytes"),
            ("0x" + ("1g" * 48), "non-hex char"),
            (" " + PK_48B + " ", "whitespace around is accepted by canonicalizer"),
        ],
    )
    def test_pubkey_length_and_hex_validation(self, pubkey: str, reason: str) -> None:
        t = NonceTable()
        if reason.startswith("whitespace"):
            t.set_last(pubkey, 1)
            assert t.get_last(PK_48B) == 1
        else:
            with pytest.raises((TypeError, ValueError)):
                t.set_last(pubkey, 1)

