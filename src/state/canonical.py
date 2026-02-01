"""
Deterministic canonical encoding primitives.

These helpers are intended for consensus-/audit-critical hashing and for
bridging data into external validators (e.g., Tau specs).
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any


CANONICAL_ENCODING_VERSION = 1

_HEX_CHARS_RE = re.compile(r"^[0-9a-fA-F]+$")


def _reject_surrogates(s: str) -> None:
    # Surrogate code points are not valid Unicode scalar values and lead to
    # implementation-defined behavior across JSON encoders/UTF-8 encoders.
    for ch in s:
        o = ord(ch)
        if 0xD800 <= o <= 0xDFFF:
            raise TypeError("surrogate code points are not allowed in canonical encoding")


def _reject_floats(value: Any) -> None:
    if isinstance(value, float):
        raise TypeError("floats are not allowed in canonical encoding")
    if isinstance(value, str):
        _reject_surrogates(value)
    if isinstance(value, dict):
        for k in value.keys():
            if not isinstance(k, str):
                raise TypeError("dict keys must be str for canonical encoding")
        for k, v in value.items():
            _reject_surrogates(k)
            _reject_floats(v)
        return
    if isinstance(value, (list, tuple)):
        for item in value:
            _reject_floats(item)
        return


def canonical_json_bytes(value: Any) -> bytes:
    """
    Canonical JSON encoding for hashing/signing.

    Rules:
    - UTF-8
    - sort_keys=True
    - separators=(',', ':') (no whitespace)
    - allow_nan=False
    - floats rejected (to avoid representation ambiguity)
    """
    _reject_floats(value)
    text = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )
    return text.encode("utf-8")


def bounded_json_utf8_size(
    value: Any,
    *,
    max_bytes: int,
    max_depth: int = 64,
    max_items: int = 200_000,
) -> int:
    """
    Best-effort upper bound on `canonical_json_bytes(value)` size, without allocating
    the full JSON string.

    Intended for DoS resistance: fail early on huge objects before calling json.dumps().
    """
    if not isinstance(max_bytes, int) or isinstance(max_bytes, bool) or max_bytes <= 0:
        raise ValueError("max_bytes must be a positive int")
    if not isinstance(max_depth, int) or isinstance(max_depth, bool) or max_depth <= 0:
        raise ValueError("max_depth must be a positive int")
    if not isinstance(max_items, int) or isinstance(max_items, bool) or max_items <= 0:
        raise ValueError("max_items must be a positive int")

    items_left = max_items

    def _ensure_budget(n: int) -> None:
        if n > max_bytes:
            raise ValueError("json size exceeds max_bytes")

    def _size_str(s: str) -> int:
        # JSON string: quotes + UTF-8 bytes + worst-case escaping overhead.
        raw_len = 0
        extra = 0
        for ch in s:
            o = ord(ch)
            if 0xD800 <= o <= 0xDFFF:
                raise TypeError("surrogate code points are not allowed in canonical encoding")
            if o < 0x80:
                raw_len += 1
            elif o < 0x800:
                raw_len += 2
            elif o < 0x10000:
                raw_len += 3
            else:
                raw_len += 4
            if ch in ('"', "\\"):
                extra += 1
            elif o < 0x20:
                # Conservative: may render as \\u00XX (6 chars) vs 1 char.
                extra += 5
            if 2 + raw_len + extra > max_bytes:
                raise ValueError("json size exceeds max_bytes")
        return 2 + raw_len + extra

    def _size(v: Any, depth: int) -> int:
        nonlocal items_left
        if depth <= 0:
            raise ValueError("json nesting exceeds max_depth")
        items_left -= 1
        if items_left < 0:
            raise ValueError("json item count exceeds max_items")

        if isinstance(v, float):
            raise TypeError("floats are not allowed in canonical encoding")
        if v is None:
            return 4  # null
        if v is True:
            return 4  # true
        if v is False:
            return 5  # false
        if isinstance(v, int) and not isinstance(v, bool):
            # Upper-bound decimal digit count without allocating `str(v)`.
            #
            # For any integer `n` with bit length `b`, `n < 2^b`, so:
            #   log10(n) < b * log10(2) < b * 0.30103
            # Therefore:
            #   digits(n) = floor(log10(n)) + 1 <= floor(b * 0.30103) + 1
            n = int(v)
            if n == 0:
                return 1
            neg = n < 0
            if neg:
                n = -n
            b = n.bit_length()
            digits = (b * 30103) // 100000 + 1
            return digits + (1 if neg else 0)
        if isinstance(v, str):
            return _size_str(v)
        if isinstance(v, (list, tuple)):
            total = 2  # []
            first = True
            for item in v:
                if not first:
                    total += 1  # comma
                first = False
                total += _size(item, depth - 1)
                _ensure_budget(total)
            return total
        if isinstance(v, dict):
            total = 2  # {}
            first = True
            for k, val in v.items():
                if not isinstance(k, str):
                    # canonical_json_bytes() will coerce some key types; reject here to keep the bound simple.
                    raise TypeError("dict keys must be str for bounded_json_utf8_size")
                if not first:
                    total += 1  # comma
                first = False
                total += _size_str(k)
                total += 1  # colon
                total += _size(val, depth - 1)
                _ensure_budget(total)
            return total
        raise TypeError(f"unsupported type for bounded_json_utf8_size: {type(v)}")

    size = _size(value, max_depth)
    _ensure_budget(size)
    return size


def sha256_hex(data: bytes) -> str:
    return "0x" + hashlib.sha256(data).hexdigest()


def domain_sep_bytes(label: str, version: int = 1) -> bytes:
    """
    Create a domain separation prefix.

    The output is ASCII-only and NUL-terminated to make concatenation unambiguous.
    """
    if not isinstance(label, str) or not label:
        raise TypeError("label must be a non-empty str")
    if "\x00" in label:
        raise ValueError("label must not contain NUL")
    try:
        label_bytes = label.encode("ascii")
    except UnicodeEncodeError as exc:
        raise ValueError("label must be ASCII") from exc
    if not isinstance(version, int) or isinstance(version, bool) or version <= 0:
        raise ValueError("version must be a positive int")
    return b"zenodex:" + label_bytes + b":v" + str(version).encode("ascii") + b"\x00"


def encode_uvarint(value: int) -> bytes:
    """Unsigned LEB128."""
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"uvarint must be a non-negative int, got {value!r}")
    out = bytearray()
    n = value
    while True:
        byte = n & 0x7F
        n >>= 7
        if n:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            break
    return bytes(out)


def encode_bytes(value: bytes) -> bytes:
    if not isinstance(value, (bytes, bytearray)):
        raise TypeError("value must be bytes")
    value_bytes = bytes(value)
    return encode_uvarint(len(value_bytes)) + value_bytes


def hex_to_bytes_fixed(hex_str: str, *, nbytes: int, name: str) -> bytes:
    if not isinstance(hex_str, str):
        raise TypeError(f"{name} must be a str")
    if not isinstance(nbytes, int) or isinstance(nbytes, bool) or nbytes <= 0:
        raise ValueError("nbytes must be a positive int")
    expected_len = 2 + 2 * nbytes
    if not hex_str.startswith("0x") or len(hex_str) != expected_len:
        raise ValueError(f"{name} must be a 0x-prefixed {nbytes}-byte hex string")
    body = hex_str[2:]
    if not _HEX_CHARS_RE.fullmatch(body):
        raise ValueError(f"{name} must be valid hex")
    try:
        out = bytes.fromhex(body)
    except ValueError as exc:
        raise ValueError(f"{name} must be valid hex") from exc
    if len(out) != nbytes:
        raise ValueError(f"{name} must decode to exactly {nbytes} bytes")
    return out


def canonical_hex_fixed_allow_0x(hex_str: str, *, nbytes: int, name: str) -> str:
    """
    Canonicalize a fixed-size hex string (lowercase, 0x-prefixed).

    Accepts either 0x-prefixed or raw hex input.
    """
    if not isinstance(hex_str, str):
        raise TypeError(f"{name} must be a str")
    if not isinstance(nbytes, int) or isinstance(nbytes, bool) or nbytes <= 0:
        raise ValueError("nbytes must be a positive int")

    s = hex_str.strip()
    if s.lower().startswith("0x"):
        s = s[2:]
    expected_len = 2 * nbytes
    if len(s) != expected_len:
        raise ValueError(f"{name} must be {nbytes} bytes (hex length {expected_len})")
    if not _HEX_CHARS_RE.fullmatch(s):
        raise ValueError(f"{name} must be valid hex")
    return "0x" + s.lower()
