"""Bounded, deterministic JSON codec for owned ZenoLacuna values.

The wire format is the plain JSON object produced by the owned dataclasses.  It
contains no schema discriminator: the public decode function selects the one
allowlisted root type, while every nested record and enum is decoded through a
fixed helper.  Decoding only creates model values after the complete JSON
shape has passed the boundary checks.
"""

from __future__ import annotations

import json
from dataclasses import fields
from enum import Enum
from typing import Final, NoReturn, TypeVar, cast

from .model import (
    Candidate,
    Decision,
    Evidence,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Policy,
    Profile,
    Question,
    Report,
    Requirement,
    Scope,
    ScopeKind,
    SourceRef,
    Witness,
    Workflow,
)

MAX_JSON_BYTES: Final = 8 * 1024 * 1024
MAX_JSON_DEPTH: Final = 32
MAX_JSON_STRING_LENGTH: Final = 4096
MAX_JSON_ARRAY_ITEMS: Final = 65_536

_ROOT_SCOPE_FIELDS: Final = frozenset(
    {
        "name",
        "contexts",
        "outcomes",
        "assumptions",
        "contract",
        "protected",
        "hypotheses",
        "questions",
        "sources",
        "profile",
        "kind",
        "history_bound",
        "omission_family",
        "max_work",
    }
)
_ROOT_CANDIDATE_FIELDS: Final = frozenset({"name", "allowed", "assumptions"})
_ROOT_DECISION_FIELDS: Final = frozenset(
    {
        "command_id",
        "scope_root",
        "parent",
        "question",
        "answer",
        "witness_root",
        "profile",
        "actor",
    }
)

_OWNED_DATACLASS_FIELDS: Final = {
    Outcome: tuple(field.name for field in fields(Outcome)),
    Requirement: tuple(field.name for field in fields(Requirement)),
    Hypothesis: tuple(field.name for field in fields(Hypothesis)),
    Question: tuple(field.name for field in fields(Question)),
    SourceRef: tuple(field.name for field in fields(SourceRef)),
    Scope: tuple(field.name for field in fields(Scope)),
    Candidate: tuple(field.name for field in fields(Candidate)),
    Witness: tuple(field.name for field in fields(Witness)),
    Policy: tuple(field.name for field in fields(Policy)),
    Report: tuple(field.name for field in fields(Report)),
    Decision: tuple(field.name for field in fields(Decision)),
}
_OWNED_ENUM_TYPES: Final = frozenset(
    {Profile, ScopeKind, OutcomeKind, Workflow, Evidence}
)


class _DuplicateJSONKey(Exception):
    pass


class _JSONFloat(Exception):
    pass


def _error(code: str) -> LacunaError:
    return LacunaError(code)


def _raise_json_type() -> NoReturn:
    raise _error("JSON_TYPE")


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise _DuplicateJSONKey
        value[key] = item
    return value


def _reject_float(_value: str) -> object:
    raise _JSONFloat


def _check_raw_depth(raw: bytes) -> None:
    """Reject excessive bracket nesting before invoking the JSON parser."""

    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == ord("\\"):
                escaped = True
            elif byte == ord('"'):
                in_string = False
            continue
        if byte == ord('"'):
            in_string = True
        elif byte in (ord("{"), ord("[")):
            depth += 1
            if depth > MAX_JSON_DEPTH:
                raise _error("JSON_DEPTH")
        elif byte in (ord("}"), ord("]")):
            depth -= 1


def _check_tree_bounds(value: object) -> None:
    """Apply container and string bounds without recursive traversal."""

    stack: list[tuple[object, int]] = [(value, 0)]
    while stack:
        current, depth = stack.pop()
        if depth > MAX_JSON_DEPTH:
            raise _error("JSON_DEPTH")
        if type(current) is str:
            _check_string(current)
        elif type(current) is list:
            if len(current) > MAX_JSON_ARRAY_ITEMS:
                raise _error("JSON_TYPE")
            stack.extend((item, depth + 1) for item in current)
        elif type(current) is dict:
            for key, item in current.items():
                if type(key) is not str:
                    _raise_json_type()
                _check_string(key)
                stack.append((item, depth + 1))
        elif current is None or type(current) is bool or type(current) is int:
            continue
        else:
            _raise_json_type()


def _parse(raw: bytes) -> object:
    if type(raw) is not bytes:
        _raise_json_type()
    if len(raw) > MAX_JSON_BYTES:
        raise _error("JSON_TOO_LARGE")
    _check_raw_depth(raw)
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise _error("JSON_INVALID") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except _DuplicateJSONKey as exc:
        raise _error("JSON_DUPLICATE_KEY") from exc
    except _JSONFloat as exc:
        raise _error("JSON_TYPE") from exc
    except (json.JSONDecodeError, RecursionError, TypeError, ValueError) as exc:
        raise _error("JSON_INVALID") from exc
    _check_tree_bounds(value)
    return value


def _check_string(value: object) -> str:
    if type(value) is not str:
        _raise_json_type()
    if len(value) > MAX_JSON_STRING_LENGTH:
        raise _error("JSON_TYPE")
    if any(0xD800 <= ord(character) <= 0xDFFF for character in value):
        raise _error("JSON_TYPE")
    return value


def _wire(value: object, depth: int = 0) -> object:
    if depth > MAX_JSON_DEPTH:
        raise _error("JSON_DEPTH")
    if value is None or type(value) is bool or type(value) is int:
        return value
    if type(value) is str:
        return _check_string(value)
    if type(value) is float:
        _raise_json_type()
    if isinstance(value, Enum):
        if type(value) not in _OWNED_ENUM_TYPES:
            raise _error("JSON_VARIANT")
        return _wire(value.value, depth + 1)
    value_type = type(value)
    if value_type in _OWNED_DATACLASS_FIELDS:
        return {
            name: _wire(getattr(value, name), depth + 1)
            for name in _OWNED_DATACLASS_FIELDS[value_type]
        }
    if type(value) is tuple or type(value) is list:
        if len(value) > MAX_JSON_ARRAY_ITEMS:
            raise _error("JSON_TYPE")
        return [_wire(item, depth + 1) for item in value]
    if type(value) is dict:
        result: dict[str, object] = {}
        for key, item in value.items():
            if type(key) is not str:
                _raise_json_type()
            _check_string(key)
            result[key] = _wire(item, depth + 1)
        return result
    _raise_json_type()


def encode(value: object) -> bytes:
    """Return canonical compact JSON bytes for an allowlisted owned value."""

    try:
        wire = _wire(value)
        encoded = json.dumps(
            wire,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except LacunaError:
        raise
    except (TypeError, ValueError, OverflowError, RecursionError) as exc:
        raise _error("JSON_TYPE") from exc
    encoded += b"\n"
    if len(encoded) > MAX_JSON_BYTES:
        raise _error("JSON_TOO_LARGE")
    return encoded


def _object(value: object, expected_fields: frozenset[str]) -> dict[str, object]:
    if type(value) is not dict:
        _raise_json_type()
    object_value = cast(dict[str, object], value)
    if set(object_value) != expected_fields:
        raise _error("JSON_FIELDS")
    return object_value


def _array(value: object) -> list[object]:
    if type(value) is not list:
        _raise_json_type()
    array_value = cast(list[object], value)
    if len(array_value) > MAX_JSON_ARRAY_ITEMS:
        raise _error("JSON_TYPE")
    return array_value


def _string(value: object) -> str:
    return _check_string(value)


def _integer(value: object) -> int:
    if type(value) is not int:
        _raise_json_type()
    return value


def _optional_integer(value: object) -> int | None:
    if value is None:
        return None
    return _integer(value)


_EnumType = TypeVar("_EnumType", bound=Enum)


def _enum_value(enum_type: type[_EnumType], value: object) -> _EnumType:
    if type(value) is not str:
        _raise_json_type()
    try:
        return enum_type(value)
    except ValueError as exc:
        raise _error("JSON_VARIANT") from exc


def _relation(value: object) -> tuple[tuple[int, ...], ...]:
    rows = _array(value)
    return tuple(tuple(_integer(item) for item in _array(row)) for row in rows)


def _outcome(value: object) -> Outcome:
    item = _object(value, frozenset({"name", "observation", "kind"}))
    return Outcome(
        _string(item["name"]),
        _string(item["observation"]),
        _enum_value(OutcomeKind, item["kind"]),
    )


def _requirement(value: object) -> Requirement:
    item = _object(value, frozenset({"name", "applicability", "allowed", "required"}))
    return Requirement(
        _string(item["name"]),
        tuple(_integer(index) for index in _array(item["applicability"])),
        _relation(item["allowed"]),
        _relation(item["required"]),
    )


def _hypothesis(value: object) -> Hypothesis:
    item = _object(value, frozenset({"name", "allowed"}))
    return Hypothesis(_string(item["name"]), _relation(item["allowed"]))


def _question(value: object) -> Question:
    item = _object(value, frozenset({"name", "prompt", "cost", "answers"}))
    return Question(
        _string(item["name"]),
        _string(item["prompt"]),
        _integer(item["cost"]),
        tuple(_string(answer) for answer in _array(item["answers"])),
    )


def _source(value: object) -> SourceRef:
    item = _object(value, frozenset({"path", "sha256"}))
    return SourceRef(_string(item["path"]), _string(item["sha256"]))


def _decode_scope(value: object) -> Scope:
    item = _object(value, _ROOT_SCOPE_FIELDS)
    outcomes = tuple(_outcome(outcome) for outcome in _array(item["outcomes"]))
    return Scope(
        _string(item["name"]),
        tuple(_string(context) for context in _array(item["contexts"])),
        outcomes,
        tuple(_integer(index) for index in _array(item["assumptions"])),
        _relation(item["contract"]),
        tuple(_requirement(requirement) for requirement in _array(item["protected"])),
        tuple(_hypothesis(hypothesis) for hypothesis in _array(item["hypotheses"])),
        tuple(_question(question) for question in _array(item["questions"])),
        tuple(_source(source) for source in _array(item["sources"])),
        _enum_value(Profile, item["profile"]),
        _enum_value(ScopeKind, item["kind"]),
        _optional_integer(item["history_bound"]),
        tuple(_string(family) for family in _array(item["omission_family"])),
        _integer(item["max_work"]),
    )


def _decode_candidate(value: object) -> Candidate:
    item = _object(value, _ROOT_CANDIDATE_FIELDS)
    return Candidate(
        _string(item["name"]),
        _relation(item["allowed"]),
        tuple(_integer(index) for index in _array(item["assumptions"])),
    )


def _decode_decision(value: object) -> Decision:
    item = _object(value, _ROOT_DECISION_FIELDS)
    return Decision(
        _string(item["command_id"]),
        _string(item["scope_root"]),
        _string(item["parent"]),
        _string(item["question"]),
        _string(item["answer"]),
        _string(item["witness_root"]),
        _enum_value(Profile, item["profile"]),
        _string(item["actor"]),
    )


def decode_scope(raw: bytes) -> Scope:
    """Decode a bounded plain JSON object into an exact :class:`Scope`."""

    return _decode_scope(_parse(raw))


def decode_candidate(raw: bytes) -> Candidate:
    """Decode a bounded plain JSON object into an exact :class:`Candidate`."""

    return _decode_candidate(_parse(raw))


def decode_decision(raw: bytes) -> Decision:
    """Decode a bounded plain JSON object into an exact :class:`Decision`."""

    return _decode_decision(_parse(raw))


__all__ = [
    "MAX_JSON_ARRAY_ITEMS",
    "MAX_JSON_BYTES",
    "MAX_JSON_DEPTH",
    "MAX_JSON_STRING_LENGTH",
    "decode_candidate",
    "decode_decision",
    "decode_scope",
    "encode",
]
