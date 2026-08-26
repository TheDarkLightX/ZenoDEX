#!/usr/bin/env python3
"""Bounded, duplicate-key-rejecting JSON decoding for release tooling.

Every limit is explicit so hostile or oversized input fails with a typed
``BoundedJsonError`` before the standard decoder allocates or recurses:

- byte length is checked before any decoding;
- a byte-level pre-scan bounds nesting depth, structural token count, and
  integer digit runs outside string literals;
- the decoder rejects duplicate object keys, floats, and non-finite constants;
- a post-decode walk counts nodes exactly and rejects lone surrogates.

The module has no filesystem, network, clock, environment, or randomness
dependencies. It is a decode boundary, not an authority.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Final

_QUOTE: Final = 0x22
_BACKSLASH: Final = 0x5C
_OPEN_BRACKETS: Final = frozenset({0x5B, 0x7B})
_CLOSE_BRACKETS: Final = frozenset({0x5D, 0x7D})
_COMMA: Final = 0x2C
_DIGIT_LOW: Final = 0x30
_DIGIT_HIGH: Final = 0x39


class BoundedJsonError(ValueError):
    """Typed rejection for input outside the declared JSON bounds."""


@dataclass(frozen=True, slots=True)
class BoundedJsonLimitsV1:
    """Closed decode limits; every field is a positive exact integer."""

    max_bytes: int
    max_depth: int
    max_nodes: int
    max_integer_digits: int

    def __post_init__(self) -> None:
        for name in ("max_bytes", "max_depth", "max_nodes", "max_integer_digits"):
            value = getattr(self, name)
            if type(value) is not int or value <= 0:
                raise TypeError(f"{name} must be a positive exact integer")


PLAN_JSON_LIMITS_V1: Final = BoundedJsonLimitsV1(
    max_bytes=4 * 1024 * 1024,
    max_depth=32,
    max_nodes=200_000,
    max_integer_digits=40,
)
GATE_OUTPUT_LIMITS_V1: Final = BoundedJsonLimitsV1(
    max_bytes=8 * 1024 * 1024,
    max_depth=32,
    max_nodes=400_000,
    max_integer_digits=40,
)


def _string_state(byte: int, escaped: bool) -> tuple[bool, bool]:
    """Advance the (in_string, escaped) automaton for one byte inside a literal."""

    if escaped:
        return True, False
    if byte == _BACKSLASH:
        return True, True
    return byte != _QUOTE, False


def _prescan_structure(payload: bytes, *, name: str, limits: BoundedJsonLimitsV1) -> None:
    """Bound depth, structural tokens, and digit runs outside string literals."""

    depth = 0
    tokens = 0
    digits = 0
    in_string = False
    escaped = False
    for byte in payload:
        if in_string:
            in_string, escaped = _string_state(byte, escaped)
            continue
        in_string = byte == _QUOTE
        depth = depth + 1 if byte in _OPEN_BRACKETS else max(depth - 1, 0) if byte in _CLOSE_BRACKETS else depth
        tokens += byte == _QUOTE or byte in _OPEN_BRACKETS or byte == _COMMA
        digits = digits + 1 if _DIGIT_LOW <= byte <= _DIGIT_HIGH else 0
        if depth > limits.max_depth:
            raise BoundedJsonError(f"{name} nesting exceeds the bound")
        if tokens > limits.max_nodes:
            raise BoundedJsonError(f"{name} node count exceeds the bound")
        if digits > limits.max_integer_digits:
            raise BoundedJsonError(f"{name} integer digits exceed the bound")


def _walk_nodes(value: object, *, name: str, limits: BoundedJsonLimitsV1) -> None:
    """Count nodes exactly and reject lone surrogates without recursion."""

    nodes = 0
    stack: list[object] = [value]
    while stack:
        item = stack.pop()
        nodes += 1
        if nodes > limits.max_nodes:
            raise BoundedJsonError(f"{name} node count exceeds the bound")
        if isinstance(item, str):
            _require_encodable(item, name=name)
        elif isinstance(item, dict):
            for key, child in item.items():
                _require_encodable(key, name=name)
                stack.append(child)
        elif isinstance(item, list):
            stack.extend(item)


def _require_encodable(text: str, *, name: str) -> None:
    try:
        text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise BoundedJsonError(f"{name} contains a lone surrogate") from exc


def decode_bounded_json_v1(
    payload: bytes,
    *,
    name: str,
    limits: BoundedJsonLimitsV1,
) -> object:
    """Decode ``payload`` under ``limits`` or raise a typed ``BoundedJsonError``.

    ``name`` labels the input in every message. The result contains only
    ``dict``, ``list``, ``str``, ``int``, ``bool``, and ``None`` values.
    """

    if type(payload) is not bytes:
        raise TypeError(f"{name} must be exact bytes")
    if len(payload) > limits.max_bytes:
        raise BoundedJsonError(f"{name} exceeds {limits.max_bytes} bytes")
    _prescan_structure(payload, name=name, limits=limits)
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise BoundedJsonError(f"{name} is not UTF-8") from exc

    def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in pairs:
            if key in result:
                raise BoundedJsonError(f"{name} contains a duplicate key")
            result[key] = item
        return result

    def reject_float(literal: str) -> object:
        raise BoundedJsonError(f"{name} contains a float")

    def reject_constant(literal: str) -> object:
        raise BoundedJsonError(f"{name} contains a non-finite constant")

    def bounded_int(literal: str) -> int:
        if len(literal.lstrip("-")) > limits.max_integer_digits:
            raise BoundedJsonError(f"{name} integer digits exceed the bound")
        return int(literal)

    try:
        value = json.loads(
            text,
            object_pairs_hook=reject_duplicate_pairs,
            parse_float=reject_float,
            parse_constant=reject_constant,
            parse_int=bounded_int,
        )
    except json.JSONDecodeError as exc:
        raise BoundedJsonError(f"{name} is not valid JSON") from exc
    except RecursionError as exc:
        raise BoundedJsonError(f"{name} nesting exceeds the bound") from exc
    _walk_nodes(value, name=name, limits=limits)
    return value
