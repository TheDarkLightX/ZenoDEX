# [TESTER] v1

from __future__ import annotations

import pytest

from src.integration.dex_engine import _hex_to_bytes_allow_0x


def test_hex_to_bytes_allow_0x_rejects_whitespace_even_if_expected_len_matches() -> None:
    # bytes.fromhex() ignores whitespace, so ensure we reject it explicitly.
    bad = "0x" + ("aa" * 47) + "  "  # 94 hex chars + 2 spaces == 96 chars (48 bytes expected)
    with pytest.raises(ValueError):
        _hex_to_bytes_allow_0x(bad, name="pubkey", expected_nbytes=48)

