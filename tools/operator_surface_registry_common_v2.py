"""Shared closed codecs and typed rejection for O-004 V2."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Final, NoReturn, cast

MAX_JSON_BYTES_V2: Final = 524_288
MAX_JSON_DEPTH_V2: Final = 32
MAX_JSON_NODES_V2: Final = 32_768
HEX_40_V2: Final = re.compile(r"[0-9a-f]{40}\Z")
HEX_64_V2: Final = re.compile(r"[0-9a-f]{64}\Z")


@dataclass(frozen=True)
class OperatorSurfaceRegistryRejectV2(ValueError):
    """Stable fail-closed rejection at an untrusted boundary."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def reject_v2(code: str, path: str, detail: str) -> NoReturn:
    raise OperatorSurfaceRegistryRejectV2(code, path, detail)


def sha256_hex_v2(raw: bytes) -> str:
    if type(raw) is not bytes:
        reject_v2("BYTES_TYPE", "sha256", "input must be exact bytes")
    return hashlib.sha256(raw).hexdigest()


def _validate_json_value_v2(
    value: object,
    *,
    depth: int = 0,
    counter: list[int] | None = None,
) -> None:
    if depth > MAX_JSON_DEPTH_V2:
        reject_v2("JSON_DEPTH", "json", "maximum depth exceeded")
    seen = counter if counter is not None else [0]
    seen[0] += 1
    if seen[0] > MAX_JSON_NODES_V2:
        reject_v2("JSON_NODE_LIMIT", "json", "maximum node count exceeded")
    if value is None or type(value) in {bool, int, str}:
        return
    if type(value) is list:
        for item in value:
            _validate_json_value_v2(item, depth=depth + 1, counter=seen)
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                reject_v2("JSON_KEY_TYPE", "json", "keys must be exact strings")
            _validate_json_value_v2(item, depth=depth + 1, counter=seen)
        return
    reject_v2("JSON_VALUE_TYPE", "json", type(value).__name__)


def canonical_json_bytes_v2(value: object) -> bytes:
    _validate_json_value_v2(value)
    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def decode_json_object_v2(raw: bytes, label: str) -> dict[str, object]:
    if type(raw) is not bytes:
        reject_v2("JSON_BYTES_TYPE", label, "input must be exact bytes")
    if len(raw) > MAX_JSON_BYTES_V2:
        reject_v2("JSON_SIZE", label, "input exceeds the fixed byte limit")

    def reject_float(_value: str) -> NoReturn:
        reject_v2("JSON_FLOAT", label, "floating point is forbidden")

    def parse_integer(value: str) -> int:
        if len(value.lstrip("-")) > 256:
            reject_v2("JSON_INTEGER_LIMIT", label, "integer is too large")
        return int(value)

    def exact_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                reject_v2("JSON_DUPLICATE_KEY", label, key)
            result[key] = value
        return result

    try:
        decoded = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=exact_object,
            parse_constant=reject_float,
            parse_float=reject_float,
            parse_int=parse_integer,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        reject_v2("JSON_DECODE", label, type(exc).__name__)
    if type(decoded) is not dict:
        reject_v2("JSON_ROOT_TYPE", label, "root must be an object")
    _validate_json_value_v2(decoded)
    return cast(dict[str, object], decoded)
