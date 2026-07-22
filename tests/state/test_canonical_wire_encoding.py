from __future__ import annotations

import pytest

from src.state.canonical import (
    CanonicalWireEncodingError,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    hex_to_bytes_fixed,
    parse_canonical_json_bytes,
    parse_canonical_json_object_bytes,
    require_canonical_hex_fixed,
)


def test_canonical_json_round_trip_accepts_exact_bytes() -> None:
    value = {
        "a": 1,
        "b": [True, "é", None],
        "nested": {"x": -7},
    }
    encoded = canonical_json_bytes(value)

    assert parse_canonical_json_bytes(encoded) == value
    assert parse_canonical_json_object_bytes(encoded) == value


@pytest.mark.parametrize(
    "transport",
    [
        b'{"b":2,"a":1}',
        b'{ "a":1,"b":2}',
        b'{"a":1,"b":2}\n',
        b'{"a":1,"a":1}',
        b'{"a":1.0}',
        b'{"a":1e0}',
        b'{"a":-0}',
        b'{"text":"\\u00e9"}',
        b'\xef\xbb\xbf{"a":1}',
    ],
)
def test_noncanonical_json_spellings_reject(transport: bytes) -> None:
    with pytest.raises(CanonicalWireEncodingError):
        parse_canonical_json_bytes(transport)


def test_canonical_json_rejects_non_object_when_object_required() -> None:
    with pytest.raises(CanonicalWireEncodingError, match="must be an object"):
        parse_canonical_json_object_bytes(b"[1,2,3]")


def test_canonical_json_rejects_duplicate_keys_before_value_loss() -> None:
    with pytest.raises(CanonicalWireEncodingError, match="duplicate JSON object key"):
        parse_canonical_json_bytes(b'{"amount":1,"amount":2}')


def test_canonical_json_transport_is_exact_bytes_only() -> None:
    with pytest.raises(TypeError, match="exact bytes"):
        parse_canonical_json_bytes(bytearray(b'{"a":1}'))  # type: ignore[arg-type]


def test_canonical_hex_has_one_accepted_spelling() -> None:
    spellings = [
        "abcd",
        "0xABCD",
        "  0xabcd  ",
        "0XABCD",
        "0xabcd",
    ]
    accepted: list[str] = []
    for spelling in spellings:
        try:
            accepted.append(
                require_canonical_hex_fixed(
                    spelling,
                    nbytes=2,
                    name="identifier",
                )
            )
        except (TypeError, ValueError):
            pass

    assert accepted == ["0xabcd"]
    assert hex_to_bytes_fixed("0xabcd", nbytes=2, name="identifier") == b"\xab\xcd"


@pytest.mark.parametrize(
    "spelling",
    ["abcd", "0xABCD", "  0xabcd  ", "0XABCD"],
)
def test_fixed_hex_byte_decoder_rejects_alternate_spellings(spelling: str) -> None:
    with pytest.raises(CanonicalWireEncodingError):
        hex_to_bytes_fixed(spelling, nbytes=2, name="identifier")


def test_permissive_hex_normalizer_is_explicitly_builder_only() -> None:
    variants = ["abcd", "0xABCD", "  0xabcd  ", "0XABCD"]
    assert {
        canonical_hex_fixed_allow_0x(value, nbytes=2, name="builder") for value in variants
    } == {"0xabcd"}
