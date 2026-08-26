from __future__ import annotations

import pytest

from tools.bounded_json_v1 import (
    GATE_OUTPUT_LIMITS_V1,
    PLAN_JSON_LIMITS_V1,
    BoundedJsonError,
    BoundedJsonLimitsV1,
    decode_bounded_json_v1,
)

SMALL = BoundedJsonLimitsV1(max_bytes=64, max_depth=3, max_nodes=5, max_integer_digits=3)


def _decode(payload: bytes, limits: BoundedJsonLimitsV1 = SMALL) -> object:
    return decode_bounded_json_v1(payload, name="fixture", limits=limits)


def test_limits_reject_non_positive_or_aliased_integers() -> None:
    # Arrange / Act / Assert
    with pytest.raises(TypeError, match="max_depth"):
        BoundedJsonLimitsV1(max_bytes=1, max_depth=0, max_nodes=1, max_integer_digits=1)
    with pytest.raises(TypeError, match="max_bytes"):
        BoundedJsonLimitsV1(max_bytes=True, max_depth=1, max_nodes=1, max_integer_digits=1)
    assert PLAN_JSON_LIMITS_V1.max_depth == GATE_OUTPUT_LIMITS_V1.max_depth == 32


def test_byte_bound_accepts_exact_limit_and_rejects_one_over() -> None:
    # Arrange
    limits = BoundedJsonLimitsV1(max_bytes=4, max_depth=3, max_nodes=5, max_integer_digits=3)

    # Act / Assert
    assert _decode(b"[12]", limits) == [12]
    with pytest.raises(BoundedJsonError, match="exceeds 4 bytes"):
        _decode(b"[123]", limits)


def test_depth_bound_accepts_exact_limit_and_rejects_one_over() -> None:
    assert _decode(b"[[[1]]]") == [[[1]]]
    with pytest.raises(BoundedJsonError, match="nesting exceeds"):
        _decode(b"[[[[1]]]]")


def test_brackets_inside_strings_do_not_count_toward_depth() -> None:
    assert _decode(b'["[[[[[", "{\\"}"]') == ["[[[[[", '{"}']


def test_node_bound_is_enforced_before_and_after_decoding() -> None:
    # Exact count 5: list + four ints.
    assert _decode(b"[1,2,3,4]") == [1, 2, 3, 4]
    # Six nodes: the post-decode walk rejects it.
    with pytest.raises(BoundedJsonError, match="node count"):
        _decode(b"[1,2,3,4,5]")
    # Structural pre-scan rejects a comma flood (43 bytes, inside the byte bound) before json.loads runs.
    with pytest.raises(BoundedJsonError, match="node count"):
        _decode(b"[" + b"1," * 20 + b"1]")


def test_integer_digit_bound_ignores_string_content() -> None:
    assert _decode(b"123") == 123
    assert _decode(b'"123456"') == "123456"
    with pytest.raises(BoundedJsonError, match="integer digits"):
        _decode(b"1234")
    with pytest.raises(BoundedJsonError, match="integer digits"):
        _decode(b"-1234")


def test_floats_and_non_finite_constants_are_rejected() -> None:
    with pytest.raises(BoundedJsonError, match="contains a float"):
        _decode(b"1.5")
    with pytest.raises(BoundedJsonError, match="contains a float"):
        _decode(b"[1e2]")
    with pytest.raises(BoundedJsonError, match="non-finite"):
        _decode(b"[NaN]")
    with pytest.raises(BoundedJsonError, match="non-finite"):
        _decode(b"Infinity")


def test_duplicate_keys_lone_surrogates_and_bad_utf8_are_rejected() -> None:
    with pytest.raises(BoundedJsonError, match="duplicate key"):
        _decode(b'{"a": 1, "a": 2}')
    with pytest.raises(BoundedJsonError, match="lone surrogate"):
        _decode(b'"\\ud800"')
    with pytest.raises(BoundedJsonError, match="lone surrogate"):
        _decode(b'{"\\udc00": 1}')
    assert _decode(b'"\\ud83d\\ude00"') == "\U0001f600"
    with pytest.raises(BoundedJsonError, match="not UTF-8"):
        _decode(b'"\xff"')


def test_malformed_json_and_non_bytes_input_are_typed_failures() -> None:
    with pytest.raises(BoundedJsonError, match="not valid JSON"):
        _decode(b"[1,]")
    with pytest.raises(BoundedJsonError, match="not valid JSON"):
        _decode(b"{} trailing")
    with pytest.raises(TypeError, match="exact bytes"):
        decode_bounded_json_v1("[]", name="fixture", limits=SMALL)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact bytes"):
        decode_bounded_json_v1(bytearray(b"[]"), name="fixture", limits=SMALL)  # type: ignore[arg-type]
