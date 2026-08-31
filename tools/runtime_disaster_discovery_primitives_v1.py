#!/usr/bin/env python3
"""Strict decoding, exact-type accessors, and canonical hashing (WholeEconomyDisasterCoverageV1).

Values only: no filesystem, subprocess, clock, environment, network, or
mutable module state.  Every rejection carries one exact ``RejectCodeV1``.
"""

from __future__ import annotations

import hashlib
import json
import re
import unicodedata
from enum import Enum
from typing import Final, Mapping, Sequence, cast

MAX_JSON_DEPTH_V1: Final = 32
MAX_TOKEN_CHARS_V1: Final = 128
MAX_PATH_CHARS_V1: Final = 512
MAX_TEXT_CHARS_V1: Final = 4096
MAX_LIST_ITEMS_V1: Final = 65536
MAX_BOUND_V1: Final = 1 << 31

_TOKEN_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:/-]{0,127}$")
_IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.]{0,127}$")
_PATH_COMPONENT_RE = re.compile(r"^[A-Za-z0-9._-]+$")
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_ROOT_RE = re.compile(r"^0x[0-9a-f]{64}$")
_GIT_OID_RE = re.compile(r"^[0-9a-f]{40}$")
_ALIAS_STRIP_RE = re.compile(r"[\s_./:\-]+")


class RejectCodeV1(str, Enum):
    """Closed, exact reject vocabulary shared by the core and both shells."""

    JSON_MALFORMED = "JSON_MALFORMED"
    JSON_ENCODING = "JSON_ENCODING"
    JSON_TOO_LARGE = "JSON_TOO_LARGE"
    JSON_TOO_DEEP = "JSON_TOO_DEEP"
    JSON_DUPLICATE_KEY = "JSON_DUPLICATE_KEY"
    JSON_FLOAT_FORBIDDEN = "JSON_FLOAT_FORBIDDEN"
    JSON_NONFINITE_FORBIDDEN = "JSON_NONFINITE_FORBIDDEN"
    TYPE_MISMATCH = "TYPE_MISMATCH"
    UNKNOWN_FIELD = "UNKNOWN_FIELD"
    MISSING_FIELD = "MISSING_FIELD"
    VALUE_OUT_OF_RANGE = "VALUE_OUT_OF_RANGE"
    TOKEN_INVALID = "TOKEN_INVALID"
    ID_DUPLICATE = "ID_DUPLICATE"
    ID_ALIAS_COLLISION = "ID_ALIAS_COLLISION"
    PATH_INVALID = "PATH_INVALID"
    PATH_NOT_REGULAR_FILE = "PATH_NOT_REGULAR_FILE"
    PATH_SYMLINK = "PATH_SYMLINK"
    PATH_DUPLICATE = "PATH_DUPLICATE"
    SCHEMA_MISMATCH = "SCHEMA_MISMATCH"
    LEGACY_BRIDGE_RECEIPT_REJECTED = "LEGACY_BRIDGE_RECEIPT_REJECTED"
    SOURCE_PIN_MISSING = "SOURCE_PIN_MISSING"
    SOURCE_PIN_UNEXPECTED = "SOURCE_PIN_UNEXPECTED"
    SOURCE_UNREADABLE = "SOURCE_UNREADABLE"
    SOURCE_HASH_DRIFT = "SOURCE_HASH_DRIFT"
    SOURCE_SIZE_DRIFT = "SOURCE_SIZE_DRIFT"
    SOURCE_BLOB_DRIFT = "SOURCE_BLOB_DRIFT"
    SOURCE_GIT_MODE_INVALID = "SOURCE_GIT_MODE_INVALID"
    SOURCE_SUBMODULE = "SOURCE_SUBMODULE"
    SOURCE_OVERSIZE = "SOURCE_OVERSIZE"
    SUBJECT_COMMIT_INVALID = "SUBJECT_COMMIT_INVALID"
    ENUMERATION_DRIFT = "ENUMERATION_DRIFT"
    AGGREGATE_FAMILY_MISSING = "AGGREGATE_FAMILY_MISSING"
    RUNNER_ARGV_FORBIDDEN = "RUNNER_ARGV_FORBIDDEN"
    RUNNER_ARGV_HASH_MISMATCH = "RUNNER_ARGV_HASH_MISMATCH"
    RUNNER_UNREGISTERED = "RUNNER_UNREGISTERED"
    RUNNER_SOURCE_UNBOUND = "RUNNER_SOURCE_UNBOUND"
    RUNNER_OBSERVATION_MISMATCH = "RUNNER_OBSERVATION_MISMATCH"
    ORACLE_UNREGISTERED = "ORACLE_UNREGISTERED"
    PREDICATE_UNREGISTERED = "PREDICATE_UNREGISTERED"
    PREDICATE_UNSPECIFIED = "PREDICATE_UNSPECIFIED"
    PREDICATE_CELL_NOT_REQUIRED = "PREDICATE_CELL_NOT_REQUIRED"
    BOUNDS_PROFILE_UNREGISTERED = "BOUNDS_PROFILE_UNREGISTERED"
    MUTANT_UNREGISTERED = "MUTANT_UNREGISTERED"
    MUTANT_SET_MISMATCH = "MUTANT_SET_MISMATCH"
    FORMAL_OBLIGATION_UNREGISTERED = "FORMAL_OBLIGATION_UNREGISTERED"
    APPLICABILITY_DECISION_INVALID = "APPLICABILITY_DECISION_INVALID"
    APPLICABILITY_DECISION_DUPLICATE = "APPLICABILITY_DECISION_DUPLICATE"
    DENOMINATOR_BELOW_FLOOR = "DENOMINATOR_BELOW_FLOOR"
    DENOMINATOR_EMPTY = "DENOMINATOR_EMPTY"
    DENOMINATOR_MISMATCH = "DENOMINATOR_MISMATCH"
    MANIFEST_INVALID = "MANIFEST_INVALID"
    MANIFEST_ROOT_DRIFT = "MANIFEST_ROOT_DRIFT"
    INVENTORY_SOURCE_INVALID = "INVENTORY_SOURCE_INVALID"
    INVENTORY_ENTRY_UNREGISTERED = "INVENTORY_ENTRY_UNREGISTERED"
    INVENTORY_ROOT_MISMATCH = "INVENTORY_ROOT_MISMATCH"
    OBLIGATION_ID_MISMATCH = "OBLIGATION_ID_MISMATCH"
    OBLIGATION_UNREGISTERED = "OBLIGATION_UNREGISTERED"
    OBLIGATION_KEY_ALIAS = "OBLIGATION_KEY_ALIAS"
    RESULT_UNEXPECTED = "RESULT_UNEXPECTED"
    RESULT_MISSING = "RESULT_MISSING"
    RESULT_DUPLICATE = "RESULT_DUPLICATE"
    RESULT_ORDER_INVALID = "RESULT_ORDER_INVALID"
    RESULT_CELL_MISMATCH = "RESULT_CELL_MISMATCH"
    PREDICATE_ROOT_MISMATCH = "PREDICATE_ROOT_MISMATCH"
    SCHEMA_ROOT_MISMATCH = "SCHEMA_ROOT_MISMATCH"
    BOUNDS_ROOT_MISMATCH = "BOUNDS_ROOT_MISMATCH"
    SOURCE_PINS_ROOT_MISMATCH = "SOURCE_PINS_ROOT_MISMATCH"
    SUBJECT_MISMATCH = "SUBJECT_MISMATCH"
    REGISTRY_STALE = "REGISTRY_STALE"
    ARTIFACT_UNBOUND = "ARTIFACT_UNBOUND"
    ARTIFACT_HASH_MISMATCH = "ARTIFACT_HASH_MISMATCH"
    NO_EFFECT_OBSERVATIONS_INCOMPLETE = "NO_EFFECT_OBSERVATIONS_INCOMPLETE"
    CALLER_PROMOTED_STATUS = "CALLER_PROMOTED_STATUS"
    CALLER_SUPPLIED_CEILING = "CALLER_SUPPLIED_CEILING"
    VM_GATE_CLOSURE_FORBIDDEN = "VM_GATE_CLOSURE_FORBIDDEN"
    WHOLE_ECONOMY_CLAIM_FORBIDDEN = "WHOLE_ECONOMY_CLAIM_FORBIDDEN"
    FLAGS_MISMATCH = "FLAGS_MISMATCH"
    RECEIPT_ROOT_MISMATCH = "RECEIPT_ROOT_MISMATCH"
    RECEIPT_CORE_MISMATCH = "RECEIPT_CORE_MISMATCH"
    PERCENTAGE_FORBIDDEN = "PERCENTAGE_FORBIDDEN"
    NONCLAIMS_MISMATCH = "NONCLAIMS_MISMATCH"
    GIT_PROBE_UNAVAILABLE = "GIT_PROBE_UNAVAILABLE"
    HEAD_MOVED = "HEAD_MOVED"
    BRIDGE_INVENTORY_UNEXTRACTABLE = "BRIDGE_INVENTORY_UNEXTRACTABLE"


class DiscoveryReject(Exception):
    """Typed fail-closed rejection carrying one exact reject code."""

    def __init__(self, code: RejectCodeV1, detail: str) -> None:
        super().__init__(f"{code.value}: {detail}")
        self.code = code
        self.detail = detail


def reject(code: RejectCodeV1, detail: str) -> DiscoveryReject:
    return DiscoveryReject(code, detail)


JsonScalar = str | int | bool | None
JsonValue = JsonScalar | list["JsonValue"] | dict[str, "JsonValue"]


# --------------------------------------------------------------------------
# Strict JSON decoding
# --------------------------------------------------------------------------


def _duplicate_key_hook(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise reject(RejectCodeV1.JSON_DUPLICATE_KEY, key)
        result[key] = value
    return result


def _float_hook(text: str) -> object:
    raise reject(RejectCodeV1.JSON_FLOAT_FORBIDDEN, text)


def _constant_hook(text: str) -> object:
    raise reject(RejectCodeV1.JSON_NONFINITE_FORBIDDEN, text)


def _check_depth(value: object, *, name: str) -> None:
    stack: list[tuple[object, int]] = [(value, 1)]
    while stack:
        current, depth = stack.pop()
        if depth > MAX_JSON_DEPTH_V1:
            raise reject(RejectCodeV1.JSON_TOO_DEEP, name)
        if type(current) is dict:
            stack.extend((item, depth + 1) for item in current.values())
        elif type(current) is list:
            stack.extend((item, depth + 1) for item in current)


def decode_strict_json(data: bytes, *, name: str, max_bytes: int) -> JsonValue:
    """Decode owned bytes once under closed JSON rules.

    Rejects oversize input, invalid UTF-8, a byte order mark, duplicate keys,
    floats, NaN or Infinity, and nesting deeper than ``MAX_JSON_DEPTH_V1``.
    """

    if type(data) is not bytes:
        raise reject(RejectCodeV1.TYPE_MISMATCH, f"{name}: bytes required")
    if len(data) > max_bytes:
        raise reject(RejectCodeV1.JSON_TOO_LARGE, f"{name}: {len(data)} bytes")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise reject(RejectCodeV1.JSON_ENCODING, f"{name}: {exc.reason}") from exc
    if text.startswith("\ufeff"):
        raise reject(RejectCodeV1.JSON_ENCODING, f"{name}: byte order mark")
    try:
        value = json.loads(
            text,
            object_pairs_hook=_duplicate_key_hook,
            parse_float=_float_hook,
            parse_constant=_constant_hook,
        )
    except RecursionError as exc:
        raise reject(RejectCodeV1.JSON_TOO_DEEP, name) from exc
    except json.JSONDecodeError as exc:
        raise reject(RejectCodeV1.JSON_MALFORMED, f"{name}: {exc.msg}") from exc
    _check_depth(value, name=name)
    return cast(JsonValue, value)


# --------------------------------------------------------------------------
# Exact-type accessors
# --------------------------------------------------------------------------


def require_object(value: object, name: str) -> Mapping[str, object]:
    if type(value) is not dict:
        raise reject(RejectCodeV1.TYPE_MISMATCH, f"{name}: object required")
    return cast(Mapping[str, object], value)


def require_closed_object(value: object, fields: Sequence[str], name: str) -> Mapping[str, object]:
    mapping = require_object(value, name)
    expected = frozenset(fields)
    unknown = sorted(set(mapping) - expected)
    if unknown:
        raise reject(RejectCodeV1.UNKNOWN_FIELD, f"{name}: {unknown}")
    missing = sorted(expected - set(mapping))
    if missing:
        raise reject(RejectCodeV1.MISSING_FIELD, f"{name}: {missing}")
    return mapping


def require_list(value: object, name: str) -> list[object]:
    if type(value) is not list:
        raise reject(RejectCodeV1.TYPE_MISMATCH, f"{name}: list required")
    if len(value) > MAX_LIST_ITEMS_V1:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}: list too long")
    return cast(list[object], value)


def require_string(value: object, name: str, *, max_chars: int = MAX_TEXT_CHARS_V1) -> str:
    if type(value) is not str:
        raise reject(RejectCodeV1.TYPE_MISMATCH, f"{name}: string required")
    if not value or len(value) > max_chars:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}: string length")
    for char in value:
        if 0xD800 <= ord(char) <= 0xDFFF:
            raise reject(RejectCodeV1.TOKEN_INVALID, f"{name}: surrogate")
    return value


def require_int(value: object, name: str, *, low: int, high: int) -> int:
    if type(value) is not int:
        raise reject(RejectCodeV1.TYPE_MISMATCH, f"{name}: exact integer required")
    if value < low or value > high:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}: {value}")
    return value


def require_bool(value: object, name: str) -> bool:
    if type(value) is not bool:
        raise reject(RejectCodeV1.TYPE_MISMATCH, f"{name}: exact boolean required")
    return value


def require_token(value: object, name: str) -> str:
    """ASCII identity token: no whitespace, no Unicode, no leading separator."""

    text = require_string(value, name, max_chars=MAX_TOKEN_CHARS_V1)
    if _TOKEN_RE.fullmatch(text) is None:
        raise reject(RejectCodeV1.TOKEN_INVALID, f"{name}: {text!r}")
    return text


def require_identifier(value: object, name: str) -> str:
    """Python-style symbol: may start with an underscore, may be dotted, ASCII only."""

    text = require_string(value, name, max_chars=MAX_TOKEN_CHARS_V1)
    if _IDENTIFIER_RE.fullmatch(text) is None:
        raise reject(RejectCodeV1.TOKEN_INVALID, f"{name}: {text!r}")
    return text


def require_enum(value: object, enum_type: type, name: str) -> object:
    text = require_token(value, name)
    try:
        return enum_type(text)
    except ValueError as exc:
        raise reject(RejectCodeV1.VALUE_OUT_OF_RANGE, f"{name}: {text}") from exc


def require_sha256(value: object, name: str) -> str:
    text = require_string(value, name, max_chars=64)
    if _SHA256_RE.fullmatch(text) is None:
        raise reject(RejectCodeV1.TOKEN_INVALID, f"{name}: sha256 hex required")
    return text


def require_root(value: object, name: str) -> str:
    text = require_string(value, name, max_chars=66)
    if _ROOT_RE.fullmatch(text) is None:
        raise reject(RejectCodeV1.TOKEN_INVALID, f"{name}: 0x root required")
    return text


def require_git_oid(value: object, name: str) -> str:
    text = require_string(value, name, max_chars=40)
    if _GIT_OID_RE.fullmatch(text) is None:
        raise reject(RejectCodeV1.TOKEN_INVALID, f"{name}: git object id required")
    return text


def require_token_list(value: object, name: str, *, unique: bool) -> tuple[str, ...]:
    items = tuple(
        require_token(item, f"{name}[{index}]")
        for index, item in enumerate(require_list(value, name))
    )
    if unique:
        require_unique_ids(items, name)
    return items


def alias_key(token: str) -> str:
    """Normalize a token so case, Unicode, separator, and whitespace variants collide."""

    return _ALIAS_STRIP_RE.sub("", unicodedata.normalize("NFKC", token)).casefold()


def require_unique_ids(ids: Sequence[str], name: str) -> None:
    seen: dict[str, str] = {}
    exact: set[str] = set()
    for item in ids:
        if item in exact:
            raise reject(RejectCodeV1.ID_DUPLICATE, f"{name}: {item}")
        exact.add(item)
        key = alias_key(item)
        if key in seen:
            raise reject(RejectCodeV1.ID_ALIAS_COLLISION, f"{name}: {seen[key]} ~ {item}")
        seen[key] = item


def validate_repo_path(value: object, name: str) -> str:
    """Accept only portable relative POSIX paths made of plain ASCII components."""

    text = require_string(value, name, max_chars=MAX_PATH_CHARS_V1)
    if text.startswith("/") or "\\" in text or "//" in text or text.endswith("/"):
        raise reject(RejectCodeV1.PATH_INVALID, f"{name}: {text!r}")
    for component in text.split("/"):
        if component in ("", ".", "..") or _PATH_COMPONENT_RE.fullmatch(component) is None:
            raise reject(RejectCodeV1.PATH_INVALID, f"{name}: {text!r}")
    return text


# --------------------------------------------------------------------------
# Canonical encoding and domain-separated hashing
# --------------------------------------------------------------------------


def _canonical_value(value: object) -> object:
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, bool) or value is None or isinstance(value, (int, str)):
        return value
    if isinstance(value, (tuple, list)):
        return [_canonical_value(item) for item in value]
    if isinstance(value, Mapping):
        result: dict[str, object] = {}
        for key in sorted(value):
            if type(key) is not str:
                raise reject(RejectCodeV1.TYPE_MISMATCH, "canonical keys must be strings")
            result[key] = _canonical_value(value[key])
        return result
    to_canonical = getattr(value, "to_canonical", None)
    if callable(to_canonical):
        return _canonical_value(to_canonical())
    raise reject(RejectCodeV1.TYPE_MISMATCH, f"non-canonical value {type(value).__name__}")


def canonical_bytes(value: object) -> bytes:
    """Sorted-key, compact, float-free UTF-8 JSON (matches src.state.canonical)."""

    text = json.dumps(
        _canonical_value(value),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )
    return text.encode("utf-8")


def domain_separator(label: str, version: int = 1) -> bytes:
    """ASCII NUL-terminated domain prefix (matches src.state.canonical.domain_sep_bytes)."""

    if not label or "\x00" in label:
        raise reject(RejectCodeV1.TOKEN_INVALID, "hash domain")
    return b"zenodex:" + label.encode("ascii") + b":v" + str(version).encode("ascii") + b"\x00"


def domain_hash_hex(domain: str, value: object) -> str:
    digest = hashlib.sha256()
    digest.update(domain_separator(domain))
    digest.update(canonical_bytes(value))
    return digest.hexdigest()


def domain_root(domain: str, value: object) -> str:
    return "0x" + domain_hash_hex(domain, value)


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_oid(data: bytes) -> str:
    """Git blob object id of exact bytes: sha1(b"blob <size>\\0" + data)."""

    header = f"blob {len(data)}\x00".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()
