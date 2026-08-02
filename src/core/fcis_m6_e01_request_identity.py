"""Typed, deterministic FCIS M6 E01 request identity.

E01 derives a stable retry identity from an authenticated-command witness and
the deployment/sequence context in which that command is presented.  The
authenticated-command and identity constructors are verifier-owned model
boundaries: ordinary callers cannot create either value by supplying raw
fields.  The external authentication verifier remains an explicit research
premise and is not implemented by this module.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final
from weakref import WeakValueDictionary

from src.state.canonical import canonical_json_bytes

FCIS_M6_E01_SCHEMA_V1: Final = "zenodex/fcis/m6/e01/request-identity/v1"
FCIS_M6_E01_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/e01/request-identity-root/v1"
MAX_E01_SENDER_BYTES_V1: Final = 128
MAX_E01_U64_V1: Final = (1 << 64) - 1
MAX_E01_U32_V1: Final = (1 << 32) - 1

_E01_COMMAND_CONSTRUCTION_TOKEN_V1 = object()
_E01_IDENTITY_CONSTRUCTION_TOKEN_V1 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")


class E01Error(ValueError):
    """Raised when an E01 value is outside its closed language."""


class E01CommandFamilyV1(str, Enum):
    """Closed command families with distinct replay namespaces."""

    STATE_CHANGE = "state_change"
    MIGRATION = "migration"
    RECOVERY = "recovery"
    AUTHORITY = "authority"
    OUTBOX_ACK = "outbox_ack"


def _text(value: object, name: str, *, maximum_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise E01Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise E01Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise E01Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise E01Error(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in _HEX_DIGITS for character in checked):
        raise E01Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _integer(value: object, name: str, *, maximum: int, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0) or value > maximum:
        raise E01Error(f"{name} is outside its closed integer bound")
    return value


def _root(body: dict[str, object]) -> str:
    return sha256(
        FCIS_M6_E01_ROOT_SCHEMA_V1.encode("ascii") + b"\x00" + canonical_json_bytes(body)
    ).hexdigest()


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E01AuthenticatedCommandV1:
    """Verifier-owned witness for one authenticated command invocation."""

    command_root: str
    sender_id: str
    command_family: E01CommandFamilyV1
    nonce: int
    authentication_profile_root: str
    authentication_evidence_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E01_COMMAND_CONSTRUCTION_TOKEN_V1:
            raise E01Error("authenticated command construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        _digest(self.command_root, "command_root")
        _text(self.sender_id, "sender_id", maximum_bytes=MAX_E01_SENDER_BYTES_V1)
        if type(self.command_family) is not E01CommandFamilyV1:
            raise E01Error("command_family has the wrong exact type")
        _integer(self.nonce, "nonce", maximum=MAX_E01_U64_V1)
        _digest(self.authentication_profile_root, "authentication_profile_root")
        _digest(self.authentication_evidence_root, "authentication_evidence_root")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            "command_root": self.command_root,
            "sender_id": self.sender_id,
            "command_family": self.command_family.value,
            "nonce": self.nonce,
            "authentication_profile_root": self.authentication_profile_root,
            "authentication_evidence_root": self.authentication_evidence_root,
        }


_E01_AUTHENTICATED_COMMANDS_V1: WeakValueDictionary[int, E01AuthenticatedCommandV1] = (
    WeakValueDictionary()
)
_E01_AUTHENTICATED_COMMAND_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _authenticated_command_snapshot_v1(
    command: E01AuthenticatedCommandV1,
) -> tuple[object, ...]:
    return (
        command.command_root,
        command.sender_id,
        command.command_family,
        command.nonce,
        command.authentication_profile_root,
        command.authentication_evidence_root,
    )


def _register_authenticated_command_v1(
    command: E01AuthenticatedCommandV1,
) -> E01AuthenticatedCommandV1:
    identity = id(command)
    _E01_AUTHENTICATED_COMMANDS_V1[identity] = command
    _E01_AUTHENTICATED_COMMAND_SNAPSHOTS_V1[identity] = _authenticated_command_snapshot_v1(command)
    return command


def _is_registered_authenticated_command_v1(value: object) -> bool:
    if type(value) is not E01AuthenticatedCommandV1:
        return False
    command = value
    registered = _E01_AUTHENTICATED_COMMANDS_V1.get(id(command))
    if registered is not command:
        return False
    try:
        command._validate_fields()
        return _E01_AUTHENTICATED_COMMAND_SNAPSHOTS_V1.get(id(command)) == (
            _authenticated_command_snapshot_v1(command)
        )
    except (AttributeError, E01Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def _mint_authenticated_command_v1(
    *,
    command_root: str,
    sender_id: str,
    command_family: E01CommandFamilyV1,
    nonce: int,
    authentication_profile_root: str,
    authentication_evidence_root: str,
) -> E01AuthenticatedCommandV1:
    """Mint the bounded model witness used by the research fixture.

    Production authentication is outside this module.  Keeping this helper
    private makes that premise visible to callers and prevents the public
    constructor from being mistaken for an authentication API.
    """

    return _register_authenticated_command_v1(
        E01AuthenticatedCommandV1(
            command_root=command_root,
            sender_id=sender_id,
            command_family=command_family,
            nonce=nonce,
            authentication_profile_root=authentication_profile_root,
            authentication_evidence_root=authentication_evidence_root,
            _construction_token=_E01_COMMAND_CONSTRUCTION_TOKEN_V1,
        )
    )


def _identity_body(
    *,
    deployment_config_root: str,
    authentication_profile_root: str,
    sender_id: str,
    command_root: str,
    command_family: E01CommandFamilyV1,
    nonce: int,
    expected_sequence: int,
    authority_epoch_index: int,
) -> dict[str, object]:
    return {
        "deployment_config_root": deployment_config_root,
        "authentication_profile_root": authentication_profile_root,
        "sender_id": sender_id,
        "command_root": command_root,
        "command_family": command_family.value,
        "nonce": nonce,
        "expected_sequence": expected_sequence,
        "authority_epoch_index": authority_epoch_index,
    }


def request_identity_body_v1(identity: E01RequestIdentityV1) -> dict[str, object]:
    """Return the canonical identity body without the self-reference."""

    if type(identity) is not E01RequestIdentityV1:
        raise E01Error("identity has the wrong exact type")
    return _identity_body(
        deployment_config_root=identity.deployment_config_root,
        authentication_profile_root=identity.authentication_profile_root,
        sender_id=identity.sender_id,
        command_root=identity.command_root,
        command_family=identity.command_family,
        nonce=identity.nonce,
        expected_sequence=identity.expected_sequence,
        authority_epoch_index=identity.authority_epoch_index,
    )


def _strict_identity_body(body: object) -> dict[str, object]:
    if type(body) is not dict:
        raise E01Error("identity body must be an exact mapping")
    expected = {
        "deployment_config_root",
        "authentication_profile_root",
        "sender_id",
        "command_root",
        "command_family",
        "nonce",
        "expected_sequence",
        "authority_epoch_index",
    }
    if set(body) != expected:
        raise E01Error("identity body fields are not exact")
    command_family_raw = body["command_family"]
    if type(command_family_raw) is not str:
        raise E01Error("command_family must be an exact string")
    try:
        command_family = E01CommandFamilyV1(command_family_raw)
    except ValueError as exc:
        raise E01Error("command_family is outside the closed enum") from exc
    return _identity_body(
        deployment_config_root=_digest(body["deployment_config_root"], "deployment_config_root"),
        authentication_profile_root=_digest(
            body["authentication_profile_root"], "authentication_profile_root"
        ),
        sender_id=_text(body["sender_id"], "sender_id", maximum_bytes=MAX_E01_SENDER_BYTES_V1),
        command_root=_digest(body["command_root"], "command_root"),
        command_family=command_family,
        nonce=_integer(body["nonce"], "nonce", maximum=MAX_E01_U64_V1),
        expected_sequence=_integer(
            body["expected_sequence"],
            "expected_sequence",
            maximum=MAX_E01_U32_V1,
            positive=True,
        ),
        authority_epoch_index=_integer(
            body["authority_epoch_index"],
            "authority_epoch_index",
            maximum=MAX_E01_U32_V1,
        ),
    )


def request_identity_root_from_body_v1(body: dict[str, object]) -> str:
    """Validate and hash one exact candidate identity body."""

    return _root(_strict_identity_body(body))


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E01RequestIdentityV1:
    """The stable identity of one authenticated request invocation."""

    deployment_config_root: str
    authentication_profile_root: str
    sender_id: str
    command_root: str
    command_family: E01CommandFamilyV1
    nonce: int
    expected_sequence: int
    authority_epoch_index: int
    request_identity_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E01_IDENTITY_CONSTRUCTION_TOKEN_V1:
            raise E01Error("request identity construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        expected_root = request_identity_root_from_body_v1(request_identity_body_v1(self))
        if _digest(self.request_identity_root, "request_identity_root") != expected_root:
            raise E01Error("request_identity_root is not canonically bound")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            "schema": FCIS_M6_E01_SCHEMA_V1,
            **request_identity_body_v1(self),
            "request_identity_root": self.request_identity_root,
        }


_E01_REQUEST_IDENTITIES_V1: WeakValueDictionary[int, E01RequestIdentityV1] = WeakValueDictionary()
_E01_REQUEST_IDENTITY_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _request_identity_snapshot_v1(identity: E01RequestIdentityV1) -> tuple[object, ...]:
    return (
        identity.deployment_config_root,
        identity.authentication_profile_root,
        identity.sender_id,
        identity.command_root,
        identity.command_family,
        identity.nonce,
        identity.expected_sequence,
        identity.authority_epoch_index,
        identity.request_identity_root,
    )


def _register_request_identity_v1(
    identity: E01RequestIdentityV1,
) -> E01RequestIdentityV1:
    identity_key = id(identity)
    _E01_REQUEST_IDENTITIES_V1[identity_key] = identity
    _E01_REQUEST_IDENTITY_SNAPSHOTS_V1[identity_key] = _request_identity_snapshot_v1(identity)
    return identity


def _is_registered_request_identity_v1(value: object) -> bool:
    if type(value) is not E01RequestIdentityV1:
        return False
    identity = value
    registered = _E01_REQUEST_IDENTITIES_V1.get(id(identity))
    if registered is not identity:
        return False
    try:
        identity._validate_fields()
        return _E01_REQUEST_IDENTITY_SNAPSHOTS_V1.get(id(identity)) == (
            _request_identity_snapshot_v1(identity)
        )
    except (AttributeError, E01Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def derive_request_identity_v1(
    *,
    authenticated_command: E01AuthenticatedCommandV1,
    deployment_config_root: str,
    expected_sequence: int,
    authority_epoch_index: int,
) -> E01RequestIdentityV1:
    """Derive one identity from a verifier-owned command and exact context."""

    if not _is_registered_authenticated_command_v1(authenticated_command):
        raise E01Error("authenticated_command lacks verifier provenance")
    if type(authenticated_command) is not E01AuthenticatedCommandV1:
        raise E01Error("authenticated_command has the wrong exact type")
    authenticated_command._validate_fields()
    checked_deployment = _digest(deployment_config_root, "deployment_config_root")
    checked_sequence = _integer(
        expected_sequence,
        "expected_sequence",
        maximum=MAX_E01_U32_V1,
        positive=True,
    )
    checked_epoch = _integer(
        authority_epoch_index,
        "authority_epoch_index",
        maximum=MAX_E01_U32_V1,
    )
    body = _identity_body(
        deployment_config_root=checked_deployment,
        authentication_profile_root=authenticated_command.authentication_profile_root,
        sender_id=authenticated_command.sender_id,
        command_root=authenticated_command.command_root,
        command_family=authenticated_command.command_family,
        nonce=authenticated_command.nonce,
        expected_sequence=checked_sequence,
        authority_epoch_index=checked_epoch,
    )
    return _register_request_identity_v1(
        E01RequestIdentityV1(
            deployment_config_root=checked_deployment,
            authentication_profile_root=authenticated_command.authentication_profile_root,
            sender_id=authenticated_command.sender_id,
            command_root=authenticated_command.command_root,
            command_family=authenticated_command.command_family,
            nonce=authenticated_command.nonce,
            expected_sequence=checked_sequence,
            authority_epoch_index=checked_epoch,
            request_identity_root=request_identity_root_from_body_v1(body),
            _construction_token=_E01_IDENTITY_CONSTRUCTION_TOKEN_V1,
        )
    )


def same_request_identity_v1(
    left: E01RequestIdentityV1,
    right: E01RequestIdentityV1,
) -> bool:
    """Return whether two typed invocations have exactly one retry identity."""

    if not _is_registered_request_identity_v1(left) or not _is_registered_request_identity_v1(
        right
    ):
        raise E01Error("identity comparison requires verifier-derived identity values")
    left._validate_fields()
    right._validate_fields()
    return left.request_identity_root == right.request_identity_root and left == right


__all__ = [
    "E01AuthenticatedCommandV1",
    "E01CommandFamilyV1",
    "E01Error",
    "E01RequestIdentityV1",
    "FCIS_M6_E01_ROOT_SCHEMA_V1",
    "FCIS_M6_E01_SCHEMA_V1",
    "derive_request_identity_v1",
    "request_identity_body_v1",
    "request_identity_root_from_body_v1",
    "same_request_identity_v1",
]
