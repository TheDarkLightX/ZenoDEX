"""
Deterministic canonical encoding primitives.

These helpers are intended for consensus-/audit-critical hashing and for
bridging data into external validators (e.g., Tau specs).
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from typing import Any

from .immutable_collections import FrozenDict as OwnedFrozenDict
from .immutable_collections import FrozenList as OwnedFrozenList
from .immutable_json import FrozenDict as JSONFrozenDict
from .immutable_json import FrozenList as JSONFrozenList

CANONICAL_ENCODING_VERSION = 1
MAX_UVARINT_BITS = 256
DEFAULT_CANONICAL_JSON_MAX_BYTES = 1_000_000

_HEX_CHARS_RE = re.compile(r"^[0-9a-fA-F]+$")
_LOWER_HEX_CHARS_RE = re.compile(r"^[0-9a-f]+$")


class CanonicalWireEncodingError(ValueError):
    """Raised when transport bytes are valid data but not the unique wire form."""


def _reject_surrogates(s: str) -> None:
    # Surrogate code points are not valid Unicode scalar values and lead to
    # implementation-defined behavior across JSON encoders/UTF-8 encoders.
    for ch in s:
        o = ord(ch)
        if 0xD800 <= o <= 0xDFFF:
            raise TypeError("surrogate code points are not allowed in canonical encoding")


def _canonical_json_projection(value: Any) -> Any:
    """Project owned immutable JSON collections into builtin encoder values."""

    if value is None or isinstance(value, (bool, int, str)):
        if isinstance(value, str):
            _reject_surrogates(value)
        return value
    if isinstance(value, float):
        raise TypeError("floats are not allowed in canonical encoding")
    if type(value) in (dict, OwnedFrozenDict, JSONFrozenDict):
        projected: dict[str, Any] = {}
        for key, child in value.items():
            if type(key) is not str:
                raise TypeError("dict keys must be str for canonical encoding")
            _reject_surrogates(key)
            projected[key] = _canonical_json_projection(child)
        return projected
    if isinstance(value, Mapping):
        raise TypeError("mapping subclasses are not allowed in canonical encoding")
    if type(value) in (list, tuple, OwnedFrozenList, JSONFrozenList):
        return [_canonical_json_projection(item) for item in value]
    if isinstance(value, (list, tuple)):
        raise TypeError("sequence subclasses are not allowed in canonical encoding")
    return value


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
    projected = _canonical_json_projection(value)
    _reject_floats(projected)
    text = json.dumps(
        projected,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )
    return text.encode("utf-8")


def _reject_duplicate_json_object_pairs(
    pairs: list[tuple[str, Any]],
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise CanonicalWireEncodingError(f"duplicate JSON object key: {key!r}")
        out[key] = value
    return out


def _reject_json_float(token: str) -> Any:
    raise CanonicalWireEncodingError(f"floating-point JSON numbers are not canonical: {token!r}")


def _reject_json_constant(token: str) -> Any:
    raise CanonicalWireEncodingError(f"non-finite JSON constant is forbidden: {token!r}")


def parse_canonical_json_bytes(
    data: bytes,
    *,
    max_bytes: int = DEFAULT_CANONICAL_JSON_MAX_BYTES,
    max_depth: int = 64,
    max_items: int = 200_000,
) -> Any:
    """Decode only the unique byte representation emitted by ``canonical_json_bytes``.

    Ordinary JSON parsing is many-to-one: whitespace, key order, duplicate keys,
    escape spelling, ``-0``, exponent notation, and byte-order marks can all decode
    to the same apparent value.  Authority-bearing input must instead satisfy:

        canonical_json_bytes(parse(data)) == data

    Duplicate keys and floating-point tokens are rejected before that equality
    check because an ordinary parser would otherwise erase their ambiguity.
    """

    if type(data) is not bytes:
        raise TypeError("canonical JSON transport must be exact bytes")
    if type(max_bytes) is not int or max_bytes <= 0:
        raise ValueError("max_bytes must be a positive exact int")
    if len(data) > max_bytes:
        raise CanonicalWireEncodingError("canonical JSON transport exceeds max_bytes")
    try:
        text = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise CanonicalWireEncodingError("canonical JSON transport must be UTF-8") from exc
    if text.startswith("\ufeff"):
        raise CanonicalWireEncodingError("canonical JSON transport must not contain a BOM")
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_json_object_pairs,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
        )
    except json.JSONDecodeError as exc:
        raise CanonicalWireEncodingError("invalid canonical JSON transport") from exc
    bounded_json_utf8_size(
        value,
        max_bytes=max_bytes,
        max_depth=max_depth,
        max_items=max_items,
    )
    if canonical_json_bytes(value) != data:
        raise CanonicalWireEncodingError(
            "JSON transport is valid but not in the unique canonical byte form"
        )
    return value


def parse_canonical_json_object_bytes(
    data: bytes,
    *,
    max_bytes: int = DEFAULT_CANONICAL_JSON_MAX_BYTES,
    max_depth: int = 64,
    max_items: int = 200_000,
) -> dict[str, Any]:
    """Decode one canonical JSON object, rejecting arrays and scalar roots."""

    value = parse_canonical_json_bytes(
        data,
        max_bytes=max_bytes,
        max_depth=max_depth,
        max_items=max_items,
    )
    if type(value) is not dict:
        raise CanonicalWireEncodingError("canonical JSON authority value must be an object")
    return value


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
    if value.bit_length() > MAX_UVARINT_BITS:
        raise ValueError(f"uvarint exceeds {MAX_UVARINT_BITS}-bit limit")
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


def require_canonical_hex_fixed(hex_str: str, *, nbytes: int, name: str) -> str:
    """Accept exactly one fixed-width hex spelling: lowercase and ``0x``-prefixed."""

    if type(hex_str) is not str:
        raise TypeError(f"{name} must be a str")
    if type(nbytes) is not int or nbytes <= 0:
        raise ValueError("nbytes must be a positive int")
    expected_len = 2 + 2 * nbytes
    if len(hex_str) != expected_len or not hex_str.startswith("0x"):
        raise CanonicalWireEncodingError(
            f"{name} must be canonical lowercase 0x-prefixed {nbytes}-byte hex"
        )
    body = hex_str[2:]
    if not _LOWER_HEX_CHARS_RE.fullmatch(body):
        raise CanonicalWireEncodingError(f"{name} must be valid hex")
    return hex_str


def hex_to_bytes_fixed(hex_str: str, *, nbytes: int, name: str) -> bytes:
    canonical = require_canonical_hex_fixed(hex_str, nbytes=nbytes, name=name)
    try:
        out = bytes.fromhex(canonical[2:])
    except ValueError as exc:  # pragma: no cover - guarded by strict syntax check
        raise CanonicalWireEncodingError(f"{name} must be valid hex") from exc
    if len(out) != nbytes:  # pragma: no cover - guarded by exact width check
        raise CanonicalWireEncodingError(f"{name} must decode to exactly {nbytes} bytes")
    return out


def canonical_hex_fixed_allow_0x(hex_str: str, *, nbytes: int, name: str) -> str:
    """Normalize builder input to fixed-width lowercase ``0x`` hex.

    This permissive helper is for pre-authority construction and authenticated
    post-processing. It is not a wire decoder. Consensus, signature, receipt, and
    persistence ingress must use ``require_canonical_hex_fixed`` or
    ``hex_to_bytes_fixed`` so only one transport spelling is accepted.
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
