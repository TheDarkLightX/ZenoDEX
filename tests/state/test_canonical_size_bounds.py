# [TESTER] v1

from __future__ import annotations

import random

import pytest

import src.state.canonical as canonical_mod
from src.state.canonical import (
    bounded_json_utf8_size,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
)


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
        {
            "nested": {
                "a": special_strings,
                "b": [random_strings[:10], {"x": random_strings[10:20]}],
            }
        },
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


def test_canonical_encoding_rejects_float_and_non_string_dict_keys() -> None:
    with pytest.raises(TypeError, match="floats are not allowed"):
        canonical_json_bytes({"x": 1.5})
    with pytest.raises(TypeError, match="dict keys must be str"):
        canonical_json_bytes({1: "x"})  # type: ignore[dict-item]


def test_bounded_json_utf8_size_rejects_invalid_limits_and_shapes() -> None:
    with pytest.raises(ValueError, match="max_bytes must be a positive int"):
        bounded_json_utf8_size({}, max_bytes=0)
    with pytest.raises(ValueError, match="max_depth must be a positive int"):
        bounded_json_utf8_size({}, max_bytes=10, max_depth=0)
    with pytest.raises(ValueError, match="max_items must be a positive int"):
        bounded_json_utf8_size({}, max_bytes=10, max_items=0)
    with pytest.raises(ValueError, match="json nesting exceeds max_depth"):
        bounded_json_utf8_size({"a": {"b": 1}}, max_bytes=100, max_depth=1)
    with pytest.raises(ValueError, match="json item count exceeds max_items"):
        bounded_json_utf8_size([1, 2], max_bytes=100, max_items=1)
    with pytest.raises(TypeError, match="dict keys must be str for bounded_json_utf8_size"):
        bounded_json_utf8_size({1: "x"}, max_bytes=100)  # type: ignore[dict-item]
    with pytest.raises(TypeError, match="unsupported type"):
        bounded_json_utf8_size(object(), max_bytes=100)


def test_domain_sep_bytes_rejects_invalid_labels_and_version() -> None:
    with pytest.raises(TypeError, match="label must be a non-empty str"):
        domain_sep_bytes("")
    with pytest.raises(ValueError, match="label must not contain NUL"):
        domain_sep_bytes("bad\x00label")
    with pytest.raises(ValueError, match="label must be ASCII"):
        domain_sep_bytes("Ω")
    with pytest.raises(ValueError, match="version must be a positive int"):
        domain_sep_bytes("ok", version=0)


def test_varint_and_bytes_encoders_reject_invalid_types() -> None:
    with pytest.raises(ValueError, match="uvarint must be a non-negative int"):
        encode_uvarint(-1)
    with pytest.raises(TypeError, match="value must be bytes"):
        encode_bytes("nope")  # type: ignore[arg-type]


def test_hex_helpers_reject_bad_type_and_can_cover_defensive_fromhex_paths(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with pytest.raises(TypeError, match="x must be a str"):
        hex_to_bytes_fixed(7, nbytes=1, name="x")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="nbytes must be a positive int"):
        hex_to_bytes_fixed("0xaa", nbytes=0, name="x")
    with pytest.raises(ValueError, match="x must be valid hex"):
        hex_to_bytes_fixed("0xzz", nbytes=1, name="x")

    class _FakeBytes:
        @staticmethod
        def fromhex(_body: str) -> bytes:
            raise ValueError("boom")

    monkeypatch.setattr(canonical_mod, "bytes", _FakeBytes, raising=False)
    with pytest.raises(ValueError, match="x must be valid hex"):
        hex_to_bytes_fixed("0xaa", nbytes=1, name="x")


def test_hex_helpers_cover_decode_length_and_canonical_allow_0x_guards(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _ShortBytes:
        @staticmethod
        def fromhex(_body: str) -> bytes:
            return b""

    monkeypatch.setattr(canonical_mod, "bytes", _ShortBytes, raising=False)
    with pytest.raises(ValueError, match="x must decode to exactly 1 bytes"):
        hex_to_bytes_fixed("0xaa", nbytes=1, name="x")

    with pytest.raises(TypeError, match="x must be a str"):
        canonical_hex_fixed_allow_0x(7, nbytes=1, name="x")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="nbytes must be a positive int"):
        canonical_hex_fixed_allow_0x("aa", nbytes=0, name="x")
