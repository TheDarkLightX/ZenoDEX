"""Typed E03 unique-commit identity for the FCIS M6 research model.

E03 keeps the datastore boundary small and explicit.  The pure side accepts
only a verifier-derived E02 nullifier, derives effect identities from the
commit/effect fields, and returns one transitively immutable aggregate.  The
SQLite transaction that persists that aggregate lives in the experiment
adapter; this module performs no I/O and makes no production-authentication
claim.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from hashlib import sha256
from typing import Final, cast
from weakref import WeakValueDictionary

from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_e02_nonce_nullifier import (
    E02Error,
    E02NullifierV1,
    is_verified_nullifier_v1,
)
from src.state.canonical import canonical_json_bytes

FCIS_M6_E03_SCHEMA_V1: Final = "zenodex/fcis/m6/e03/unique-commit-port/v1"
FCIS_M6_E03_FINGERPRINT_SCHEMA_V1: Final = "zenodex/fcis/m6/e03/commit-fingerprint/v1"
MAX_E03_TRANSITIONS_V1: Final = dra.MAX_TRANSITIONS
MAX_E03_EFFECTS_V1: Final = dra.MAX_OUTBOX_PER_TRANSITION
MAX_E03_DESTINATION_BYTES_V1: Final = dra.MAX_TEXT_BYTES
MAX_E03_U32_V1: Final = dra.U32_MAX
_HEX_DIGITS = frozenset("0123456789abcdef")

_E03_COMMIT_CONSTRUCTION_TOKEN_V1 = object()
_E03_COMMIT_REGISTRY_V1: WeakValueDictionary[int, E03CommitIdentityV1] = WeakValueDictionary()
_E03_COMMIT_SNAPSHOTS_V1: dict[int, bytes] = {}


class E03Error(ValueError):
    """Raised when an E03 identity or effect is outside its closed domain."""


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _HEX_DIGITS for character in value)
    ):
        raise E03Error(f"{name} must be a lowercase SHA-256 digest")
    return value


def _text(value: object, name: str, *, maximum_bytes: int) -> str:
    if type(value) is not str or not value:
        raise E03Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise E03Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise E03Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise E03Error(f"{name} contains a control character")
    return value


def _u32(value: object, name: str, *, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum or value > MAX_E03_U32_V1:
        raise E03Error(f"{name} is outside its closed u32 bound")
    return value


@dataclass(frozen=True, slots=True, order=True)
class E03EffectSpecV1:
    """Effect fields from which the semantic effect identity is derived."""

    ordinal: int
    destination: str
    payload_root: str
    writer_profile_root: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        ordinal = _u32(self.ordinal, "ordinal")
        if ordinal >= MAX_E03_EFFECTS_V1:
            raise E03Error("ordinal exceeds the E03 per-commit bound")
        _text(
            self.destination,
            "destination",
            maximum_bytes=MAX_E03_DESTINATION_BYTES_V1,
        )
        _digest(self.payload_root, "payload_root")
        _digest(self.writer_profile_root, "writer_profile_root")
        _digest(self.adapter_profile_root, "adapter_profile_root")

    def derive_effect_id(self, commit_id: str) -> str:
        """Derive this effect's ID from the owning commit and its ordinal."""

        return cast(
            str,
            dra.derive_effect_id(
                commit_id=commit_id,
                ordinal=self.ordinal,
                destination=self.destination,
                payload_root=self.payload_root,
                writer_profile_root=self.writer_profile_root,
                adapter_profile_root=self.adapter_profile_root,
            ),
        )

    def to_wire(self, *, commit_id: str) -> dict[str, object]:
        self.__post_init__()
        return {
            "effect_id": self.derive_effect_id(commit_id),
            "ordinal": self.ordinal,
            "destination": self.destination,
            "payload_root": self.payload_root,
            "writer_profile_root": self.writer_profile_root,
            "adapter_profile_root": self.adapter_profile_root,
        }


def _fingerprint_body(value: E03CommitIdentityV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_E03_SCHEMA_V1,
        "sequence": value.sequence,
        "commit_id": value.commit_id,
        "nullifier_root": value.nullifier.nullifier_root,
        "request_identity_root": value.nullifier.request_identity_root,
        "effects": [effect.to_wire(commit_id=value.commit_id) for effect in value.effects],
    }


def _fingerprint(value: E03CommitIdentityV1) -> str:
    return sha256(
        FCIS_M6_E03_FINGERPRINT_SCHEMA_V1.encode("ascii")
        + b"\x00"
        + canonical_json_bytes(_fingerprint_body(value))
    ).hexdigest()


@dataclass(frozen=True, slots=True, weakref_slot=True)
class E03CommitIdentityV1:
    """Verifier-owned aggregate persisted by the E03 unique commit port."""

    sequence: int
    commit_id: str
    nullifier: E02NullifierV1
    effects: tuple[E03EffectSpecV1, ...]
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _E03_COMMIT_CONSTRUCTION_TOKEN_V1:
            raise E03Error("E03 commit identity construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        sequence = _u32(self.sequence, "sequence", minimum=1)
        if sequence > MAX_E03_TRANSITIONS_V1:
            raise E03Error("sequence exceeds the E03 transition bound")
        _digest(self.commit_id, "commit_id")
        if type(self.nullifier) is not E02NullifierV1:
            raise E03Error("nullifier has the wrong exact type")
        if not is_verified_nullifier_v1(self.nullifier):
            raise E03Error("nullifier lacks verifier provenance")
        if type(self.effects) is not tuple:
            raise E03Error("effects must be an exact tuple")
        if len(self.effects) > MAX_E03_EFFECTS_V1:
            raise E03Error("effects exceed the E03 per-commit bound")
        if any(type(effect) is not E03EffectSpecV1 for effect in self.effects):
            raise E03Error("effects contain a value with the wrong exact type")
        for effect in self.effects:
            effect.__post_init__()
        if tuple(sorted(self.effects, key=lambda effect: effect.ordinal)) != self.effects:
            raise E03Error("effects must be in ordinal order")
        if tuple(effect.ordinal for effect in self.effects) != tuple(range(len(self.effects))):
            raise E03Error("effect ordinals must be contiguous from zero")
        effect_ids = tuple(effect.derive_effect_id(self.commit_id) for effect in self.effects)
        if len(set(effect_ids)) != len(effect_ids):
            raise E03Error("effect identities must be unique within the commit")

    @property
    def fingerprint(self) -> str:
        """Return the canonical identity fingerprint for the complete aggregate."""

        self._validate_fields()
        return _fingerprint(self)

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            "schema": FCIS_M6_E03_SCHEMA_V1,
            "sequence": self.sequence,
            "commit_id": self.commit_id,
            "nullifier_root": self.nullifier.nullifier_root,
            "request_identity_root": self.nullifier.request_identity_root,
            "fingerprint": self.fingerprint,
            "effects": [effect.to_wire(commit_id=self.commit_id) for effect in self.effects],
        }


def _register_commit_v1(value: E03CommitIdentityV1) -> E03CommitIdentityV1:
    key = id(value)
    _E03_COMMIT_REGISTRY_V1[key] = value
    _E03_COMMIT_SNAPSHOTS_V1[key] = canonical_json_bytes(value.to_wire())
    return value


def _mint_e03_commit_identity_v1(
    *,
    sequence: int,
    commit_id: str,
    nullifier: E02NullifierV1,
    effects: tuple[E03EffectSpecV1, ...],
) -> E03CommitIdentityV1:
    """Mint the bounded E03 witness from the preceding verifier-owned value."""

    if not is_verified_nullifier_v1(nullifier):
        raise E03Error("E02 nullifier must be verifier-derived")
    return _register_commit_v1(
        E03CommitIdentityV1(
            sequence=sequence,
            commit_id=commit_id,
            nullifier=nullifier,
            effects=effects,
            _construction_token=_E03_COMMIT_CONSTRUCTION_TOKEN_V1,
        )
    )


def is_verified_e03_commit_identity_v1(value: object) -> bool:
    """Return whether ``value`` is an unchanged verifier-derived aggregate."""

    if type(value) is not E03CommitIdentityV1:
        return False
    identity = value
    if _E03_COMMIT_REGISTRY_V1.get(id(identity)) is not identity:
        return False
    try:
        identity._validate_fields()
        expected = _E03_COMMIT_SNAPSHOTS_V1.get(id(identity))
        return expected is not None and expected == cast(
            bytes, canonical_json_bytes(identity.to_wire())
        )
    except (AttributeError, E02Error, E03Error, TypeError, ValueError, ArithmeticError):
        return False


__all__ = (
    "E03CommitIdentityV1",
    "E03EffectSpecV1",
    "E03Error",
    "FCIS_M6_E03_FINGERPRINT_SCHEMA_V1",
    "FCIS_M6_E03_SCHEMA_V1",
    "MAX_E03_DESTINATION_BYTES_V1",
    "MAX_E03_EFFECTS_V1",
    "MAX_E03_TRANSITIONS_V1",
    "MAX_E03_U32_V1",
    "is_verified_e03_commit_identity_v1",
)
