"""Bounded signed commands for the ZenoLacuna approval boundary.

This module is a functional codec and verifier.  It has no filesystem, clock,
network, or key lookup authority: callers provide the pinned owner key, the
current scope root, and the already parsed delegation records explicitly.
"""

from __future__ import annotations

import base64
import hashlib
import json
import re
from dataclasses import dataclass
from enum import StrEnum
from typing import Final, NoReturn, cast

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)

from .model import LacunaError

PROTOCOL_VERSION: Final[int] = 1
MAX_PAYLOAD_BYTES: Final[int] = 8 * 1024 * 1024
MAX_WIRE_BYTES: Final[int] = 12 * 1024 * 1024
MAX_JSON_DEPTH: Final[int] = 32
MAX_PROJECT_ID_LENGTH: Final[int] = 128

_KEY_HEX_LENGTH: Final[int] = 64
_SIGNATURE_HEX_LENGTH: Final[int] = 128
_ROOT_PATTERN: Final[re.Pattern[str]] = re.compile(r"[0-9a-f]{64}")
_KEY_PATTERN: Final[re.Pattern[str]] = re.compile(r"[0-9a-f]{64}")
_SIGNATURE_PATTERN: Final[re.Pattern[str]] = re.compile(r"[0-9a-f]{128}")
_PROJECT_PATTERN: Final[re.Pattern[str]] = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:-]{0,127}")

_COMMAND_FIELDS: Final[frozenset[str]] = frozenset(
    {"action", "parent", "payload", "project_id", "version"}
)
_SIGNED_FIELDS: Final[frozenset[str]] = frozenset(
    {"command", "public_key", "signature", "version"}
)
_DELEGATION_FIELDS: Final[frozenset[str]] = frozenset(
    {"actions", "public_key", "scope_root", "version"}
)
_ACTION_ORDER: Final[tuple[str, ...]] = (
    "INIT",
    "ANSWER",
    "REVISE",
    "ASSESS",
    "COMPLETE",
    "CANCEL",
    "RESUME",
)
_ACTION_INDEX: Final[dict[str, int]] = {value: index for index, value in enumerate(_ACTION_ORDER)}
_DELEGATE_ACTIONS: Final[frozenset[str]] = frozenset({"ANSWER", "ASSESS", "COMPLETE"})
_COMMAND_ROOT_DOMAIN: Final[bytes] = b"zenolacuna/approval-command-root/v1\x00"
_COMMAND_SIGNATURE_DOMAIN: Final[bytes] = b"zenolacuna/approval-command-signature/v1\x00"


class Action(StrEnum):
    """Closed command lifecycle variants."""

    INIT = "INIT"
    ANSWER = "ANSWER"
    REVISE = "REVISE"
    ASSESS = "ASSESS"
    COMPLETE = "COMPLETE"
    CANCEL = "CANCEL"
    RESUME = "RESUME"


class _DuplicateJSONKey(Exception):
    pass


class _JSONFloat(Exception):
    pass


def _malformed() -> NoReturn:
    raise LacunaError("MALFORMED_APPROVAL")


def _invalid_signature() -> NoReturn:
    raise LacunaError("INVALID_SIGNATURE")


def _unauthorized() -> NoReturn:
    raise LacunaError("UNAUTHORIZED")


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise _DuplicateJSONKey
        value[key] = item
    return value


def _reject_float(_value: str) -> object:
    raise _JSONFloat


def _check_depth(raw: bytes) -> None:
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
                _malformed()
        elif byte in (ord("}"), ord("]")):
            depth -= 1


def _check_tree(value: object) -> None:
    stack: list[tuple[object, int]] = [(value, 0)]
    while stack:
        current, depth = stack.pop()
        if depth > MAX_JSON_DEPTH:
            _malformed()
        if type(current) is str:
            if any(0xD800 <= ord(character) <= 0xDFFF for character in current):
                _malformed()
        elif type(current) is list:
            stack.extend((item, depth + 1) for item in cast(list[object], current))
        elif type(current) is dict:
            for key, item in cast(dict[str, object], current).items():
                if type(key) is not str:
                    _malformed()
                if any(0xD800 <= ord(character) <= 0xDFFF for character in key):
                    _malformed()
                stack.append((item, depth + 1))
        elif current is None or type(current) is bool or type(current) is int:
            continue
        else:
            _malformed()


def _canonical_json(value: object) -> bytes:
    try:
        return json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("ascii") + b"\n"
    except (TypeError, ValueError, OverflowError, UnicodeError, RecursionError) as exc:
        raise LacunaError("MALFORMED_APPROVAL") from exc


def _parse_object(raw: bytes, maximum: int) -> dict[str, object]:
    if type(raw) is not bytes or len(raw) > maximum:
        _malformed()
    _check_depth(raw)
    try:
        text = raw.decode("ascii")
        value = json.loads(
            text,
            object_pairs_hook=_unique_object,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (_DuplicateJSONKey, _JSONFloat, UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError, TypeError) as exc:
        raise LacunaError("MALFORMED_APPROVAL") from exc
    _check_tree(value)
    if type(value) is not dict or _canonical_json(value) != raw:
        _malformed()
    return cast(dict[str, object], value)


def _closed_object(value: object, fields: frozenset[str]) -> dict[str, object]:
    if type(value) is not dict:
        _malformed()
    result = cast(dict[str, object], value)
    if set(result) != fields:
        _malformed()
    return result


def _version(value: object) -> None:
    if type(value) is not int or value != PROTOCOL_VERSION:
        _malformed()


def _root(value: object) -> str:
    if type(value) is not str or _ROOT_PATTERN.fullmatch(value) is None:
        _malformed()
    return value


def _key(value: object) -> str:
    if type(value) is not str or len(value) != _KEY_HEX_LENGTH or _KEY_PATTERN.fullmatch(value) is None:
        _malformed()
    return value


def _signature(value: object) -> str:
    if type(value) is not str or len(value) != _SIGNATURE_HEX_LENGTH or _SIGNATURE_PATTERN.fullmatch(value) is None:
        _malformed()
    return value


def _project_id(value: object) -> str:
    if type(value) is not str or not 1 <= len(value) <= MAX_PROJECT_ID_LENGTH:
        _malformed()
    if _PROJECT_PATTERN.fullmatch(value) is None:
        _malformed()
    return value


def _action(value: object) -> Action:
    if type(value) is not str:
        _malformed()
    try:
        return Action(value)
    except ValueError as exc:
        raise LacunaError("MALFORMED_APPROVAL") from exc


def _payload(value: object) -> bytes:
    if type(value) is not bytes or len(value) > MAX_PAYLOAD_BYTES:
        _malformed()
    raw = value
    parsed = _parse_object(raw, MAX_PAYLOAD_BYTES)
    if _canonical_json(parsed) != raw:
        _malformed()
    return raw


@dataclass(frozen=True, slots=True)
class Command:
    """Canonical, typed command data signed by an owner or delegate."""

    project_id: str
    parent: str | None
    action: Action
    payload: bytes

    def __post_init__(self) -> None:
        _project_id(self.project_id)
        if self.parent is not None:
            _root(self.parent)
        if type(self.action) is not Action:
            _malformed()
        _payload(self.payload)


@dataclass(frozen=True, slots=True)
class SignedCommand:
    """A command and its raw Ed25519 public key/signature encodings."""

    command: Command
    public_key: str
    signature: str

    def __post_init__(self) -> None:
        if type(self.command) is not Command:
            _malformed()
        _key(self.public_key)
        _signature(self.signature)


@dataclass(frozen=True, slots=True)
class Delegation:
    """A capability scoped to one root and a canonical action tuple."""

    public_key: str
    scope_root: str
    actions: tuple[Action, ...]

    def __post_init__(self) -> None:
        _key(self.public_key)
        _root(self.scope_root)
        if type(self.actions) is not tuple:
            _malformed()
        previous = -1
        seen: set[Action] = set()
        for action in self.actions:
            if type(action) is not Action:
                _malformed()
            if action in seen or _ACTION_INDEX[action.value] <= previous:
                _malformed()
            seen.add(action)
            previous = _ACTION_INDEX[action.value]


def _ensure_command(command: object) -> Command:
    if type(command) is not Command:
        _malformed()
    return command


def _ensure_signed(signed: object) -> SignedCommand:
    if type(signed) is not SignedCommand:
        _malformed()
    return signed


def _command_wire(command: Command) -> dict[str, object]:
    return {
        "action": command.action.value,
        "parent": command.parent,
        "payload": base64.b64encode(command.payload).decode("ascii"),
        "project_id": command.project_id,
        "version": PROTOCOL_VERSION,
    }


def command_bytes(command: Command) -> bytes:
    """Return the canonical versioned bytes covered by a signature and root."""

    return _canonical_json(_command_wire(_ensure_command(command)))


def command_root(command: Command) -> str:
    """Return a domain-separated SHA-256 root for the complete command."""

    return hashlib.sha256(_COMMAND_ROOT_DOMAIN + command_bytes(command)).hexdigest()


def _signature_message(command: Command) -> bytes:
    return _COMMAND_SIGNATURE_DOMAIN + command_bytes(command)


def sign(command: Command, private_key_bytes: bytes) -> SignedCommand:
    """Sign a command with an Ed25519 seed supplied by the imperative shell."""

    checked_command = _ensure_command(command)
    if type(private_key_bytes) is not bytes or len(private_key_bytes) != 32:
        _malformed()
    try:
        private_key = Ed25519PrivateKey.from_private_bytes(private_key_bytes)
        public_key = private_key.public_key().public_bytes(
            serialization.Encoding.Raw,
            serialization.PublicFormat.Raw,
        ).hex()
        signature = private_key.sign(_signature_message(checked_command)).hex()
    except (TypeError, ValueError, OverflowError) as exc:
        raise LacunaError("MALFORMED_APPROVAL") from exc
    return SignedCommand(checked_command, public_key, signature)


def _decode_payload_b64(value: object) -> bytes:
    if type(value) is not str:
        _malformed()
    try:
        raw = base64.b64decode(value.encode("ascii"), validate=True)
    except (UnicodeEncodeError, ValueError, TypeError) as exc:
        raise LacunaError("MALFORMED_APPROVAL") from exc
    if len(raw) > MAX_PAYLOAD_BYTES or base64.b64encode(raw).decode("ascii") != value:
        _malformed()
    return raw


def encode_signed(signed: SignedCommand) -> bytes:
    """Return the canonical bounded signed-command envelope."""

    checked = _ensure_signed(signed)
    value = {
        "command": _command_wire(checked.command),
        "public_key": checked.public_key,
        "signature": checked.signature,
        "version": PROTOCOL_VERSION,
    }
    encoded = _canonical_json(value)
    if len(encoded) > MAX_WIRE_BYTES:
        _malformed()
    return encoded


def decode_signed(raw: bytes) -> SignedCommand:
    """Decode one exact canonical signed-command envelope."""

    value = _parse_object(raw, MAX_WIRE_BYTES)
    outer = _closed_object(value, _SIGNED_FIELDS)
    _version(outer["version"])
    command_value = _closed_object(outer["command"], _COMMAND_FIELDS)
    _version(command_value["version"])
    command = Command(
        _project_id(command_value["project_id"]),
        None if command_value["parent"] is None else _root(command_value["parent"]),
        _action(command_value["action"]),
        _payload(_decode_payload_b64(command_value["payload"])),
    )
    signed = SignedCommand(command, _key(outer["public_key"]), _signature(outer["signature"]))
    if encode_signed(signed) != raw:
        _malformed()
    return signed


def encode_delegation(delegation: Delegation) -> bytes:
    """Encode a delegation for inclusion in an owner-approved payload."""

    checked = delegation
    if type(checked) is not Delegation:
        _malformed()
    value = {
        "actions": [action.value for action in checked.actions],
        "public_key": checked.public_key,
        "scope_root": checked.scope_root,
        "version": PROTOCOL_VERSION,
    }
    encoded = _canonical_json(value)
    if len(encoded) > MAX_WIRE_BYTES:
        _malformed()
    return encoded


def decode_delegation(raw: bytes) -> Delegation:
    """Decode one exact canonical delegation record."""

    value = _parse_object(raw, MAX_WIRE_BYTES)
    item = _closed_object(value, _DELEGATION_FIELDS)
    _version(item["version"])
    actions_value = item["actions"]
    if type(actions_value) is not list:
        _malformed()
    actions: list[Action] = []
    for value_item in cast(list[object], actions_value):
        actions.append(_action(value_item))
    delegation = Delegation(_key(item["public_key"]), _root(item["scope_root"]), tuple(actions))
    if encode_delegation(delegation) != raw:
        _malformed()
    return delegation


def _check_external_context(owner_key: object, delegates: object, scope_root: object) -> tuple[str, tuple[Delegation, ...], str]:
    if type(owner_key) is not str or _KEY_PATTERN.fullmatch(owner_key) is None:
        _malformed()
    if type(scope_root) is not str or _ROOT_PATTERN.fullmatch(scope_root) is None:
        _malformed()
    if type(delegates) is not tuple:
        _malformed()
    checked_delegates: list[Delegation] = []
    for delegation in cast(tuple[object, ...], delegates):
        if type(delegation) is not Delegation:
            _malformed()
        checked_delegates.append(delegation)
    return owner_key, tuple(checked_delegates), scope_root


def _verify_signature(signed: SignedCommand) -> None:
    try:
        public_key = Ed25519PublicKey.from_public_bytes(bytes.fromhex(signed.public_key))
        public_key.verify(bytes.fromhex(signed.signature), _signature_message(signed.command))
    except (InvalidSignature, ValueError, TypeError, OverflowError):
        _invalid_signature()


def verify(
    signed: SignedCommand,
    *,
    owner_key: str,
    delegates: tuple[Delegation, ...],
    scope_root: str,
) -> None:
    """Verify cryptography, then apply the externally supplied authority map.

    The payload remains opaque here.  A caller may parse owner-approved
    delegation data at the lifecycle boundary, while arbitrary payload fields
    never mint authority inside this function.
    """

    checked = _ensure_signed(signed)
    _verify_signature(checked)
    checked_owner, checked_delegates, checked_scope = _check_external_context(owner_key, delegates, scope_root)
    if checked.public_key == checked_owner:
        return
    action = checked.command.action.value
    if action not in _DELEGATE_ACTIONS:
        _unauthorized()
    for delegation in checked_delegates:
        if (
            delegation.public_key == checked.public_key
            and delegation.scope_root == checked_scope
            and checked.command.action in delegation.actions
        ):
            return
    _unauthorized()


__all__ = [
    "Action",
    "Command",
    "Delegation",
    "MAX_JSON_DEPTH",
    "MAX_PAYLOAD_BYTES",
    "MAX_PROJECT_ID_LENGTH",
    "MAX_WIRE_BYTES",
    "PROTOCOL_VERSION",
    "SignedCommand",
    "command_bytes",
    "command_root",
    "decode_delegation",
    "decode_signed",
    "encode_delegation",
    "encode_signed",
    "sign",
    "verify",
]
