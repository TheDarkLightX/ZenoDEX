"""Canonical immutable journal records. Decoding never establishes decision authority."""

from __future__ import annotations

import base64
import hashlib
import json
import re
from dataclasses import dataclass, replace
from typing import Final, NoReturn, cast

from .codec import _check_raw_depth
from .model import LacunaError


def _raise(code: str) -> NoReturn:
    raise LacunaError(code)


_RECORD_VERSION: Final = 1



_RECORD_PREFIX: Final = b"zenolacuna/record/v1\x00"



_REVISION_PREFIX: Final = b"zenolacuna/revision/v1\x00"



_RECORD_PATTERN: Final = re.compile(r"[0-9a-f]{64}")



_OPERATIONS: Final = frozenset(
    {"INIT", "ANSWER", "ASSESS_REPAIR", "REPLAY", "CANCEL", "RESUME"}
)



_MAX_RECORD_BYTES: Final = 12 * 1024 * 1024



_MAX_ATTEMPTS: Final = 4_096



@dataclass(frozen=True, slots=True)
class _Record:
    revision: str
    parent: str | None
    operation: str
    scope_bytes: bytes | None
    decision_bytes: bytes | None
    candidate_bytes: bytes | None
    checker_hash: str
    attempt: int



class _DuplicateKey(Exception):
    pass



class _FloatValue(Exception):
    pass



def _canonical_json(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("ascii") + b"\n"



def _hash(prefix: bytes, value: bytes) -> str:
    return hashlib.sha256(prefix + value).hexdigest()



def _is_digest(value: object) -> bool:
    return type(value) is str and _RECORD_PATTERN.fullmatch(value) is not None



def _b64(value: bytes | None) -> str | None:
    return None if value is None else base64.b64encode(value).decode("ascii")



def _decode_b64(value: object) -> bytes | None:
    if value is None:
        return None
    if type(value) is not str or len(value) > 2 * _MAX_RECORD_BYTES:
        _raise("CORRUPT_RECORD")
    try:
        raw = base64.b64decode(value.encode("ascii"), validate=True)
    except (UnicodeEncodeError, ValueError) as exc:
        raise LacunaError("CORRUPT_RECORD") from exc
    if len(raw) > _MAX_RECORD_BYTES or _b64(raw) != value:
        _raise("CORRUPT_RECORD")
    return raw



def _record_payload(record: _Record) -> dict[str, object]:
    return {
        "attempt": record.attempt,
        "candidate": _b64(record.candidate_bytes),
        "checker_hash": record.checker_hash,
        "decision": _b64(record.decision_bytes),
        "operation": record.operation,
        "parent": record.parent,
        "scope": _b64(record.scope_bytes),
        "version": _RECORD_VERSION,
    }



def _record_bytes(record: _Record) -> bytes:
    payload = _record_payload(record)
    body = {"payload": payload, "revision": record.revision}
    return _canonical_json({"checksum": _hash(_RECORD_PREFIX, _canonical_json(body)), **body})



def _record_for(
    parent: str | None,
    operation: str,
    *,
    scope_bytes: bytes | None,
    decision_bytes: bytes | None,
    candidate_bytes: bytes | None,
    checker_hash: str,
    attempt: int,
) -> _Record:
    provisional = _Record(
        revision="0" * 64,
        parent=parent,
        operation=operation,
        scope_bytes=scope_bytes,
        decision_bytes=decision_bytes,
        candidate_bytes=candidate_bytes,
        checker_hash=checker_hash,
        attempt=attempt,
    )
    revision = _hash(_REVISION_PREFIX, _canonical_json(_record_payload(provisional)))
    return replace(provisional, revision=revision)



def _record_byte_cost(record: _Record, serialized_bytes: int) -> int:
    """Count stored JSON and its decoded typed payload bytes together."""
    return serialized_bytes + sum(
        len(value)
        for value in (record.scope_bytes, record.decision_bytes, record.candidate_bytes)
        if value is not None
    )



def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateKey
        result[key] = value
    return result



def _reject_float(_value: str) -> object:
    raise _FloatValue



def _record_from_bytes(raw: bytes) -> _Record:
    if len(raw) > _MAX_RECORD_BYTES:
        _raise("CORRUPT_RECORD")
    try:
        _check_raw_depth(raw)
        decoded = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (_DuplicateKey, _FloatValue, UnicodeDecodeError, json.JSONDecodeError, TypeError, ValueError, RecursionError) as exc:
        raise LacunaError("CORRUPT_RECORD") from exc
    if type(decoded) is not dict or raw != _canonical_json(decoded):
        _raise("CORRUPT_RECORD")
    outer = cast(dict[str, object], decoded)
    if set(outer) != {"checksum", "payload", "revision"}:
        _raise("CORRUPT_RECORD")
    checksum = outer["checksum"]
    revision = outer["revision"]
    payload_value = outer["payload"]
    if type(payload_value) is not dict or not _is_digest(checksum) or not _is_digest(revision):
        _raise("CORRUPT_RECORD")
    payload = cast(dict[str, object], payload_value)
    if set(payload) != {
        "attempt",
        "candidate",
        "checker_hash",
        "decision",
        "operation",
        "parent",
        "scope",
        "version",
    }:
        _raise("CORRUPT_RECORD")
    if type(payload["version"]) is not int or payload["version"] != _RECORD_VERSION:
        _raise("CORRUPT_RECORD")
    attempt = payload["attempt"]
    operation = payload["operation"]
    parent = payload["parent"]
    checker_hash = payload["checker_hash"]
    if (
        type(attempt) is not int
        or not 0 <= attempt <= _MAX_ATTEMPTS
        or type(operation) is not str
        or operation not in _OPERATIONS
        or (parent is not None and not _is_digest(parent))
        or not _is_digest(checker_hash)
    ):
        _raise("CORRUPT_RECORD")
    body = {"payload": payload, "revision": revision}
    if checksum != _hash(_RECORD_PREFIX, _canonical_json(body)):
        _raise("CORRUPT_RECORD")
    record = _Record(
        revision=cast(str, revision),
        parent=cast(str | None, parent),
        operation=operation,
        scope_bytes=_decode_b64(payload["scope"]),
        decision_bytes=_decode_b64(payload["decision"]),
        candidate_bytes=_decode_b64(payload["candidate"]),
        checker_hash=cast(str, checker_hash),
        attempt=attempt,
    )
    if record.revision != _hash(_REVISION_PREFIX, _canonical_json(_record_payload(record))):
        _raise("CORRUPT_RECORD")
    return record
