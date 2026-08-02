"""Typed FCIS M6 E02 nonce-to-nullifier relation.

E02 binds one verifier-derived E01 request identity to the next sender nonce
and derives exactly one deployment/family-scoped nullifier.  The module is a
research-only functional-core boundary: it does not consume a production
nonce, insert a datastore row, or authenticate a signature.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from hashlib import sha256
from typing import Final
from weakref import WeakValueDictionary

from src.core.fcis_m6_e01_request_identity import (
    E01CommandFamilyV1,
    E01Error,
    E01RequestIdentityV1,
    same_request_identity_v1,
)
from src.state.canonical import canonical_json_bytes

FCIS_M6_E02_SCHEMA_V1: Final = "zenodex/fcis/m6/e02/nonce-nullifier/v1"
FCIS_M6_E02_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/e02/nullifier-root/v1"
MAX_E02_U64_V1: Final = (1 << 64) - 1
MAX_E02_CURRENT_NONCE_V1: Final = MAX_E02_U64_V1 - 1
MAX_E02_SENDER_BYTES_V1: Final = 128

_E02_NULLIFIER_CONSTRUCTION_TOKEN_V1 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")


class E02Error(ValueError):
    """Raised when an E02 input is outside the closed relation."""


def _text(value: object, name: str, *, maximum_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise E02Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise E02Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise E02Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise E02Error(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in _HEX_DIGITS for character in checked):
        raise E02Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _integer(value: object, name: str, *, maximum: int, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0) or value > maximum:
        raise E02Error(f"{name} is outside its closed integer bound")
    return value


def _nullifier_body(
    *,
    deployment_config_root: str,
    sender_id: str,
    command_family: E01CommandFamilyV1,
    nonce: int,
) -> dict[str, object]:
    return {
        "deployment_config_root": deployment_config_root,
        "sender_id": sender_id,
        "nonce": nonce,
        "command_family": command_family.value,
    }


def _nullifier_root(body: dict[str, object]) -> str:
    return sha256(
        FCIS_M6_E02_ROOT_SCHEMA_V1.encode("ascii") + b"\x00" + canonical_json_bytes(body)
    ).hexdigest()


def _strict_nullifier_body(body: object) -> dict[str, object]:
    if type(body) is not dict:
        raise E02Error("nullifier body must be an exact mapping")
    expected = {
        "deployment_config_root",
        "sender_id",
        "nonce",
        "command_family",
    }
    if set(body) != expected:
        raise E02Error("nullifier body fields are not exact")
    family_raw = body["command_family"]
    if type(family_raw) is not str:
        raise E02Error("command_family must be an exact string")
    try:
        family = E01CommandFamilyV1(family_raw)
    except ValueError as exc:
        raise E02Error("command_family is outside the closed enum") from exc
    return _nullifier_body(
        deployment_config_root=_digest(body["deployment_config_root"], "deployment_config_root"),
        sender_id=_text(body["sender_id"], "sender_id", maximum_bytes=MAX_E02_SENDER_BYTES_V1),
        command_family=family,
        nonce=_integer(body["nonce"], "nonce", maximum=MAX_E02_U64_V1, positive=True),
    )


def nullifier_root_from_body_v1(body: dict[str, object]) -> str:
    """Validate one exact nullifier preimage and return its canonical root."""

    return _nullifier_root(_strict_nullifier_body(body))


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E02NullifierV1:
    """Verifier-owned nullifier witness for one E01 request identity."""

    deployment_config_root: str
    sender_id: str
    command_family: E01CommandFamilyV1
    nonce: int
    request_identity_root: str
    nullifier_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E02_NULLIFIER_CONSTRUCTION_TOKEN_V1:
            raise E02Error("nullifier construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        _digest(self.deployment_config_root, "deployment_config_root")
        _text(self.sender_id, "sender_id", maximum_bytes=MAX_E02_SENDER_BYTES_V1)
        if type(self.command_family) is not E01CommandFamilyV1:
            raise E02Error("command_family has the wrong exact type")
        _integer(self.nonce, "nonce", maximum=MAX_E02_U64_V1, positive=True)
        _digest(self.request_identity_root, "request_identity_root")
        expected_root = nullifier_root_from_body_v1(self.preimage_body())
        if _digest(self.nullifier_root, "nullifier_root") != expected_root:
            raise E02Error("nullifier_root is not canonically bound")

    def preimage_body(self) -> dict[str, object]:
        return _nullifier_body(
            deployment_config_root=self.deployment_config_root,
            sender_id=self.sender_id,
            command_family=self.command_family,
            nonce=self.nonce,
        )

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            "schema": FCIS_M6_E02_SCHEMA_V1,
            **self.preimage_body(),
            "request_identity_root": self.request_identity_root,
            "nullifier_root": self.nullifier_root,
        }


_E02_NULLIFIERS_V1: WeakValueDictionary[int, E02NullifierV1] = WeakValueDictionary()
_E02_NULLIFIER_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _nullifier_snapshot_v1(value: E02NullifierV1) -> tuple[object, ...]:
    return (
        value.deployment_config_root,
        value.sender_id,
        value.command_family,
        value.nonce,
        value.request_identity_root,
        value.nullifier_root,
    )


def _register_nullifier_v1(value: E02NullifierV1) -> E02NullifierV1:
    key = id(value)
    _E02_NULLIFIERS_V1[key] = value
    _E02_NULLIFIER_SNAPSHOTS_V1[key] = _nullifier_snapshot_v1(value)
    return value


def is_verified_nullifier_v1(value: object) -> bool:
    """Return whether ``value`` is an unchanged verifier-derived witness."""

    if type(value) is not E02NullifierV1:
        return False
    nullifier = value
    if _E02_NULLIFIERS_V1.get(id(nullifier)) is not nullifier:
        return False
    try:
        nullifier._validate_fields()
        return _E02_NULLIFIER_SNAPSHOTS_V1.get(id(nullifier)) == _nullifier_snapshot_v1(nullifier)
    except (AttributeError, E02Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def _require_verified_request_identity_v1(value: object) -> E01RequestIdentityV1:
    if type(value) is not E01RequestIdentityV1:
        raise E02Error("request identity has the wrong exact type")
    identity = value
    try:
        same_request_identity_v1(identity, identity)
    except (E01Error, TypeError, ValueError, ArithmeticError, OverflowError) as exc:
        raise E02Error("request identity lacks verifier provenance") from exc
    return identity


def derive_nonce_nullifier_v1(
    *,
    request_identity: E01RequestIdentityV1,
    current_nonce: int,
) -> E02NullifierV1:
    """Derive the next sender nullifier from a verified E01 identity.

    The relation is exact: ``request_identity.nonce == current_nonce + 1``.
    The increment is checked before evaluation, so the maximum u64 nonce
    cannot wrap into an accepted value.  ``current_nonce`` is state supplied
    by the research fixture and is not consumed or persisted here.
    """

    identity = _require_verified_request_identity_v1(request_identity)
    checked_current = _integer(
        current_nonce,
        "current_nonce",
        maximum=MAX_E02_CURRENT_NONCE_V1,
    )
    expected_nonce = checked_current + 1
    if identity.nonce != expected_nonce:
        raise E02Error("command nonce is not the exact next sender nonce")
    body = _nullifier_body(
        deployment_config_root=identity.deployment_config_root,
        sender_id=identity.sender_id,
        command_family=identity.command_family,
        nonce=identity.nonce,
    )
    return _register_nullifier_v1(
        E02NullifierV1(
            deployment_config_root=identity.deployment_config_root,
            sender_id=identity.sender_id,
            command_family=identity.command_family,
            nonce=identity.nonce,
            request_identity_root=identity.request_identity_root,
            nullifier_root=_nullifier_root(body),
            _construction_token=_E02_NULLIFIER_CONSTRUCTION_TOKEN_V1,
        )
    )


def same_nullifier_v1(left: E02NullifierV1, right: E02NullifierV1) -> bool:
    """Compare only verifier-derived nullifier witnesses."""

    if not is_verified_nullifier_v1(left) or not is_verified_nullifier_v1(right):
        raise E02Error("nullifier comparison requires verifier-derived values")
    left._validate_fields()
    right._validate_fields()
    return left == right and left.nullifier_root == right.nullifier_root


__all__ = [
    "E02Error",
    "E02NullifierV1",
    "FCIS_M6_E02_ROOT_SCHEMA_V1",
    "FCIS_M6_E02_SCHEMA_V1",
    "MAX_E02_CURRENT_NONCE_V1",
    "MAX_E02_U64_V1",
    "derive_nonce_nullifier_v1",
    "is_verified_nullifier_v1",
    "nullifier_root_from_body_v1",
    "same_nullifier_v1",
]
