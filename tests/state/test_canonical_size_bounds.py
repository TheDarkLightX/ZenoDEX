# [TESTER] v1

from __future__ import annotations

import random

import pytest

from src.state.canonical import bounded_json_utf8_size, canonical_json_bytes, hex_to_bytes_fixed


def test_bounded_json_utf8_size_never_underestimates_canonical_json_bytes() -> None:
    # This test is a guardrail for DoS pre-checks that rely on bounded_json_utf8_size()
    # before calling canonical_json_bytes(). The bound must never be smaller than the
    # actual canonical encoding size for supported inputs.
    #
    # Focus on tricky escaping and UTF-8 edge cases.
    special_strings = [
        "",
        "ascii",
        '"',
        "\\",
        "\n",
        "\r",
        "\t",
        "\x00",
        "\x01",
        "\x1f",
        "line\u2028sep",
        "para\u2029sep",
        "emoji😀",
        "multi-byte: ΩЖ中😀",
    ]

    rng = random.Random(0)
    random_strings: list[str] = []
    for _ in range(200):
        # Include control chars + high bytes; decode via latin1 to preserve 0-255.
        b = bytes(rng.randrange(0, 256) for _ in range(rng.randrange(0, 64)))
        random_strings.append(b.decode("latin1"))

    values = [
        None,
        True,
        False,
        0,
        1,
        -1,
        123456789012345678901234567890,
        *special_strings,
        *random_strings,
        {"k": "v"},
        {"k": special_strings},
        {"nested": {"a": special_strings, "b": [random_strings[:10], {"x": random_strings[10:20]}]}},
        [special_strings, random_strings[:20], {"k": random_strings[20:40]}],
    ]

    for v in values:
        actual = len(canonical_json_bytes(v))
        est = bounded_json_utf8_size(v, max_bytes=10**9)
        assert est >= actual


def test_canonical_encoding_rejects_surrogate_code_points() -> None:
    v = {"s": "\ud800"}  # lone surrogate
    with pytest.raises(TypeError, match="surrogate"):
        canonical_json_bytes(v)
    with pytest.raises(TypeError, match="surrogate"):
        bounded_json_utf8_size(v, max_bytes=1000)


def test_hex_to_bytes_fixed_rejects_whitespace_even_if_length_matches() -> None:
    # bytes.fromhex() ignores whitespace, so ensure we reject it explicitly.
    with pytest.raises(ValueError):
        hex_to_bytes_fixed("0xAA  ", nbytes=2, name="x")
