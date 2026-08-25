"""Boundary evidence for the shared global-economic canonical JSON decoder."""

from __future__ import annotations

import json
from collections.abc import Callable

import pytest

import src.core.global_economic_durable_activation_v1 as activation_module
from src.core.global_economic_durable_activation_v1 import (
    MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1,
    _decode_exact_canonical_json_v1,
)


def _nested_array(depth: int, leaf: bytes = b"null") -> bytes:
    return (b"[" * depth) + leaf + (b"]" * depth)


def _nested_object(depth: int, leaf: bytes = b"null") -> bytes:
    return (b'{"k":' * depth) + leaf + (b"}" * depth)


def _alternating_containers(depth: int, leaf: bytes = b"null") -> bytes:
    payload = leaf
    for index in reversed(range(depth)):
        payload = (b"[" + payload + b"]") if index % 2 == 0 else (b'{"k":' + payload + b"}")
    return payload


def test_canonical_json_depth_bva_accepts_maximum_and_rejects_next_depth() -> None:
    # Arrange: canonical arrays at max-1, max, and max+1 container depth.
    below = _nested_array(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1 - 1)
    maximum = _nested_array(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1)
    above = _nested_array(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1 + 1)

    # Act and assert: the pinned Python runtime accepts the inclusive array bound.
    _decode_exact_canonical_json_v1(below, name="below-boundary")
    _decode_exact_canonical_json_v1(maximum, name="at-boundary")
    with pytest.raises(ValueError, match="above-boundary JSON nesting exceeds"):
        _decode_exact_canonical_json_v1(above, name="above-boundary")


def test_canonical_json_depth_rejection_precedes_host_recursion_behavior() -> None:
    # Arrange: a shape that previously escaped the shared decoder as RecursionError.
    hostile = _nested_array(1_500)

    # Act and assert: the pinned runtime receives the typed resource rejection.
    with pytest.raises(ValueError, match="hostile JSON nesting exceeds the bound"):
        _decode_exact_canonical_json_v1(hostile, name="hostile")


@pytest.mark.parametrize("builder", [_nested_object, _alternating_containers])
def test_canonical_json_depth_bva_covers_objects_and_mixed_containers(
    builder: Callable[[int], bytes],
) -> None:
    # Arrange: object-bearing structures at max-1, max, and max+1 depth.
    below = builder(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1 - 1)
    maximum = builder(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1)
    above = builder(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1 + 1)

    # Act and assert: an array-only scanner mutant cannot satisfy this boundary.
    _decode_exact_canonical_json_v1(below, name="below-object-boundary")
    _decode_exact_canonical_json_v1(maximum, name="at-object-boundary")
    with pytest.raises(ValueError, match="above-object-boundary JSON nesting exceeds"):
        _decode_exact_canonical_json_v1(above, name="above-object-boundary")


@pytest.mark.parametrize(
    "string_value",
    [
        ("[{" * 80) + ("}]" * 80),
        ("\\" * 7) + '"' + ("[" * 80),
        ("\\" * 8) + '"' + ("{" * 80),
    ],
)
def test_canonical_json_depth_scanner_ignores_string_delimiters_at_real_limit(
    string_value: str,
) -> None:
    # Arrange: real depth is exactly the limit; the leaf contains many fake delimiters.
    leaf = json.dumps(string_value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    payload = _nested_array(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1, leaf)

    # Act: decode through the same canonical boundary used by authority journals.
    decoded = _decode_exact_canonical_json_v1(payload, name="string-delimiters")

    # Assert: a scanner that counts delimiters in strings would reject this valid payload.
    cursor = decoded
    for _ in range(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1):
        assert isinstance(cursor, list) and len(cursor) == 1
        cursor = cursor[0]
    assert cursor == string_value


def test_backslash_before_closing_quote_preserves_following_container_depth_bva() -> None:
    # Arrange: the first array item is a JSON string ending in a decoded backslash.
    # Its source has an even backslash run before the closing quote. A scanner
    # that checks only the immediately previous character stays inside the string
    # and misses the following real containers.
    escaped_leaf = json.dumps("\\", separators=(",", ":")).encode("utf-8")
    at_limit = (
        b"["
        + escaped_leaf
        + b","
        + _nested_array(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1 - 1)
        + b"]"
    )
    above_limit = (
        b"["
        + escaped_leaf
        + b","
        + _nested_array(MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1)
        + b"]"
    )

    # Act and assert: total depth 64 is accepted and total depth 65 rejects.
    decoded = _decode_exact_canonical_json_v1(at_limit, name="backslash-at-limit")
    with pytest.raises(ValueError, match="backslash-above-limit JSON nesting exceeds"):
        _decode_exact_canonical_json_v1(above_limit, name="backslash-above-limit")
    assert isinstance(decoded, list) and decoded[0] == "\\"


def test_canonicalization_recursion_is_normalized_to_typed_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: emulate a supported-runtime mismatch in the recursive canonicalizer.
    def recurse(_value: object) -> bytes:
        raise RecursionError("host recursion capacity")

    monkeypatch.setattr(activation_module, "canonical_global_bytes_v1", recurse)

    # Act and assert: host recursion never escapes the untrusted decode boundary.
    with pytest.raises(ValueError, match="canonicalization exceeds the host recursion capacity"):
        _decode_exact_canonical_json_v1(b"null", name="host-boundary")


def test_malformed_overdeep_json_has_deterministic_resource_rejection() -> None:
    # Arrange: malformed JSON exceeds the resource bound before syntax completion.
    hostile = b"[" * (MAX_GLOBAL_ECONOMIC_CANONICAL_JSON_DEPTH_V1 + 1)

    # Act and assert: rejection precedence stays resource-first and parser-independent.
    with pytest.raises(ValueError, match="malformed JSON nesting exceeds the bound"):
        _decode_exact_canonical_json_v1(hostile, name="malformed")
