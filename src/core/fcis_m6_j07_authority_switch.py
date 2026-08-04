"""Typed FCIS M6 J07 authority-switch and stale-token research relation.

J07 consumes the verifier-owned J06 quiescence gate and a freshly rechecked
F06 migration authorization.  It emits one canonical pre/post relation in
which the phase, authority epoch, active writer profile, head, and snapshot
change together.  The relation is an isolated refinement target; it does not
provide a production transaction or a runtime writer middleware.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, NoReturn, TypeAlias, cast
from weakref import WeakValueDictionary

from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_f06_reopen_authorization import (
    F06AuthorizationRejectV1,
    F06AuthorizationTokenV1,
    F06AuthorizationUseV1,
    F06OperationV1,
    require_f06_token_at_use,
)
from src.core.fcis_m6_j06_quiescence import (
    J06QuiescenceGateV1,
    is_verified_quiescence_gate_v1,
)
from src.core.fcis_m6_writer_profile_eligibility_v1 import (
    WriterProfileEligibilityReceiptV1,
    is_verified_writer_profile_eligibility_receipt_v1,
)
from src.state.canonical import canonical_json_bytes

FCIS_M6_J07_SCHEMA_V1: Final = "zenodex/fcis/m6/j07/authority-switch/v1"
FCIS_M6_J07_CONTEXT_SCHEMA_V1: Final = "zenodex/fcis/m6/j07/authority-context/v1"
FCIS_M6_J07_TOKEN_SCHEMA_V1: Final = "zenodex/fcis/m6/j07/writer-token/v1"
FCIS_M6_J07_TOKEN_SCHEMA_V2: Final = "zenodex/fcis/m6/j07/writer-token/v2"
FCIS_M6_J07_SWITCH_SCHEMA_V1: Final = "zenodex/fcis/m6/j07/switch-result/v1"
MAX_J07_SEQUENCE_V1: Final = (1 << 32) - 1
MAX_J07_PATH_PARTS_V1: Final = 8

_J07_CONTEXT_CONSTRUCTION_TOKEN_V1 = object()
_J07_TOKEN_CONSTRUCTION_TOKEN_V2 = object()
_J07_DECISION_CONSTRUCTION_TOKEN_V1 = object()
_J07_SWITCH_CONSTRUCTION_TOKEN_V1 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")


class J07Error(ValueError):
    """Raised when a J07 value is outside its closed research language."""


class J07StateKindV1(str, Enum):
    """The only two states exposed by the isolated switch relation."""

    PRE_QUIESCED = "pre_quiesced"
    POST_AUTHORITY_SWITCH = "post_authority_switch"


class J07RejectCodeV1(str, Enum):
    """Closed rejection classes for switch and writer admission."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    GATE_REJECTED = "gate_rejected"
    GATE_PHASE_REJECTED = "gate_phase_rejected"
    AUTHORIZATION_REJECTED = "authorization_rejected"
    AUTHORIZATION_HEAD_MISMATCH = "authorization_head_mismatch"
    AUTHORIZATION_SNAPSHOT_MISMATCH = "authorization_snapshot_mismatch"
    AUTHORIZATION_AUTHORITY_MISMATCH = "authorization_authority_mismatch"
    AUTHORIZATION_EPOCH_MISMATCH = "authorization_epoch_mismatch"
    PROFILE_COLLISION = "profile_collision"
    CONTEXT_REJECTED = "context_rejected"
    TOKEN_REJECTED = "token_rejected"
    ELIGIBILITY_REJECTED = "eligibility_rejected"
    ELIGIBILITY_CONTEXT_MISMATCH = "eligibility_context_mismatch"
    STALE_TOKEN = "stale_token"
    WRITER_PROFILE_DISABLED = "writer_profile_disabled"


def _text(value: object, name: str, *, maximum_bytes: int = 256) -> str:
    if type(value) is not str or not value:
        raise J07Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise J07Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise J07Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise J07Error(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in _HEX_DIGITS for character in checked):
        raise J07Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    minimum = 1 if positive else 0
    if type(value) is not int or value < minimum or value > MAX_J07_SEQUENCE_V1:
        raise J07Error(f"{name} is outside its closed u32 bound")
    return value


def _path(value: object, name: str) -> tuple[str, ...]:
    if type(value) is not tuple or not value:
        raise J07Error(f"{name} must be a nonempty exact tuple")
    if len(value) > MAX_J07_PATH_PARTS_V1:
        raise J07Error(f"{name} exceeds its closed collection bound")
    return tuple(
        _text(item, f"{name}[{index}]", maximum_bytes=64) for index, item in enumerate(value)
    )


def _root(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=66)
    if (
        len(checked) != 66
        or not checked.startswith("0x")
        or checked != checked.lower()
        or any(character not in _HEX_DIGITS for character in checked[2:])
    ):
        raise J07Error(f"{name} must be a lowercase 0x-prefixed 32-byte root")
    return checked


def _strip_f06_root(value: object, name: str) -> str:
    checked = _root(value, name)
    return checked[2:]


def _derive(domain: str, payload: dict[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(payload)).hexdigest()


def _context_body(context: J07AuthorityContextV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_J07_CONTEXT_SCHEMA_V1,
        "kind": context.kind.value,
        "phase": context.phase.value,
        "epoch_index": context.epoch_index,
        "legacy_profile_root": context.legacy_profile_root,
        "target_profile_root": context.target_profile_root,
        "active_profile_root": context.active_profile_root,
        "allowed_writer_roots": list(context.allowed_writer_roots),
        "authority_state_root": context.authority_state_root,
        "current_head_root": context.current_head_root,
        "current_snapshot_root": context.current_snapshot_root,
        "current_state_root": context.current_state_root,
        "deployment_config_root": context.deployment_config_root,
        "previous_epoch_index": context.previous_epoch_index,
        "previous_authority_state_root": context.previous_authority_state_root,
        "previous_head_root": context.previous_head_root,
        "previous_snapshot_root": context.previous_snapshot_root,
        "previous_state_root": context.previous_state_root,
        "previous_deployment_config_root": context.previous_deployment_config_root,
        "gate_root": context.gate_root,
        "migration_token_root": context.migration_token_root,
        "activation_sequence": context.activation_sequence,
    }


def _context_root(context: J07AuthorityContextV1) -> str:
    return _derive("zenodex/fcis/m6/j07/context", _context_body(context))


def _context_values_body(values: dict[str, object]) -> dict[str, object]:
    return {
        "schema": FCIS_M6_J07_CONTEXT_SCHEMA_V1,
        "kind": cast(J07StateKindV1, values["kind"]).value,
        "phase": cast(dra.MigrationPhaseV1, values["phase"]).value,
        "epoch_index": values["epoch_index"],
        "legacy_profile_root": values["legacy_profile_root"],
        "target_profile_root": values["target_profile_root"],
        "active_profile_root": values["active_profile_root"],
        "allowed_writer_roots": list(cast(tuple[str, ...], values["allowed_writer_roots"])),
        "authority_state_root": values["authority_state_root"],
        "current_head_root": values["current_head_root"],
        "current_snapshot_root": values["current_snapshot_root"],
        "current_state_root": values["current_state_root"],
        "deployment_config_root": values["deployment_config_root"],
        "previous_epoch_index": values["previous_epoch_index"],
        "previous_authority_state_root": values["previous_authority_state_root"],
        "previous_head_root": values["previous_head_root"],
        "previous_snapshot_root": values["previous_snapshot_root"],
        "previous_state_root": values["previous_state_root"],
        "previous_deployment_config_root": values["previous_deployment_config_root"],
        "gate_root": values["gate_root"],
        "migration_token_root": values["migration_token_root"],
        "activation_sequence": values["activation_sequence"],
    }


def _context_from_values(values: dict[str, object]) -> J07AuthorityContextV1:
    context_root = _derive("zenodex/fcis/m6/j07/context", _context_values_body(values))
    return J07AuthorityContextV1(
        kind=cast(J07StateKindV1, values["kind"]),
        phase=cast(dra.MigrationPhaseV1, values["phase"]),
        epoch_index=cast(int, values["epoch_index"]),
        legacy_profile_root=cast(str, values["legacy_profile_root"]),
        target_profile_root=cast(str, values["target_profile_root"]),
        active_profile_root=cast(str, values["active_profile_root"]),
        allowed_writer_roots=cast(tuple[str, ...], values["allowed_writer_roots"]),
        authority_state_root=cast(str, values["authority_state_root"]),
        current_head_root=cast(str, values["current_head_root"]),
        current_snapshot_root=cast(str, values["current_snapshot_root"]),
        current_state_root=cast(str, values["current_state_root"]),
        deployment_config_root=cast(str, values["deployment_config_root"]),
        previous_epoch_index=cast(int, values["previous_epoch_index"]),
        previous_authority_state_root=cast(str, values["previous_authority_state_root"]),
        previous_head_root=cast(str, values["previous_head_root"]),
        previous_snapshot_root=cast(str, values["previous_snapshot_root"]),
        previous_state_root=cast(str, values["previous_state_root"]),
        previous_deployment_config_root=cast(str, values["previous_deployment_config_root"]),
        gate_root=cast(str, values["gate_root"]),
        migration_token_root=cast(str, values["migration_token_root"]),
        activation_sequence=cast(int, values["activation_sequence"]),
        context_root=context_root,
        _construction_token=_J07_CONTEXT_CONSTRUCTION_TOKEN_V1,
    )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class J07AuthorityContextV1:
    """Verifier-owned pre/post authority context for one switch atom."""

    kind: J07StateKindV1
    phase: dra.MigrationPhaseV1
    epoch_index: int
    legacy_profile_root: str
    target_profile_root: str
    active_profile_root: str
    allowed_writer_roots: tuple[str, ...]
    authority_state_root: str
    current_head_root: str
    current_snapshot_root: str
    current_state_root: str
    deployment_config_root: str
    previous_epoch_index: int
    previous_authority_state_root: str
    previous_head_root: str
    previous_snapshot_root: str
    previous_state_root: str
    previous_deployment_config_root: str
    gate_root: str
    migration_token_root: str
    activation_sequence: int
    context_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J07_CONTEXT_CONSTRUCTION_TOKEN_V1:
            raise J07Error("authority-context construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        if type(self.kind) is not J07StateKindV1:
            raise J07Error("kind has the wrong exact type")
        if type(self.phase) is not dra.MigrationPhaseV1:
            raise J07Error("phase has the wrong exact type")
        _u32(self.epoch_index, "epoch_index")
        _u32(self.previous_epoch_index, "previous_epoch_index")
        _u32(self.activation_sequence, "activation_sequence", positive=True)
        for name in (
            "legacy_profile_root",
            "target_profile_root",
            "active_profile_root",
            "authority_state_root",
            "current_head_root",
            "current_snapshot_root",
            "current_state_root",
            "deployment_config_root",
            "previous_authority_state_root",
            "previous_head_root",
            "previous_snapshot_root",
            "previous_state_root",
            "previous_deployment_config_root",
            "gate_root",
            "migration_token_root",
            "context_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        if self.legacy_profile_root == self.target_profile_root:
            raise J07Error("legacy and target profiles must differ")
        if type(self.allowed_writer_roots) is not tuple:
            raise J07Error("allowed_writer_roots must be an exact tuple")
        if len(self.allowed_writer_roots) > 1:
            raise J07Error("J07 allows at most one active writer profile")
        for index, writer in enumerate(self.allowed_writer_roots):
            _digest(writer, f"allowed_writer_roots[{index}]")
        if self.kind is J07StateKindV1.PRE_QUIESCED:
            if self.phase is not dra.MigrationPhaseV1.QUIESCED:
                raise J07Error("pre context must be QUIESCED")
            if self.epoch_index != self.previous_epoch_index:
                raise J07Error("pre context epoch changed")
            if self.active_profile_root != self.legacy_profile_root:
                raise J07Error("pre context active profile is not legacy")
            if self.allowed_writer_roots:
                raise J07Error("pre context must have no value-moving writer")
            if any(
                current != previous
                for current, previous in (
                    (self.authority_state_root, self.previous_authority_state_root),
                    (self.current_head_root, self.previous_head_root),
                    (self.current_snapshot_root, self.previous_snapshot_root),
                    (self.current_state_root, self.previous_state_root),
                    (self.deployment_config_root, self.previous_deployment_config_root),
                )
            ):
                raise J07Error("pre context has a predecessor mismatch")
        elif self.kind is J07StateKindV1.POST_AUTHORITY_SWITCH:
            if self.phase is not dra.MigrationPhaseV1.AUTHORITY_SWITCH:
                raise J07Error("post context must be AUTHORITY_SWITCH")
            if self.epoch_index != self.previous_epoch_index + 1:
                raise J07Error("post context epoch did not advance exactly once")
            if self.active_profile_root != self.target_profile_root:
                raise J07Error("post context active profile is not target")
            if self.allowed_writer_roots != (self.target_profile_root,):
                raise J07Error("post context writer set is not target-only")
            if self.current_state_root != self.previous_state_root:
                raise J07Error("post context changed the current state root")
            if self.deployment_config_root != self.previous_deployment_config_root:
                raise J07Error("post context changed the deployment root")
            if self.authority_state_root == self.previous_authority_state_root:
                raise J07Error("authority root did not change at switch")
            if self.current_head_root == self.previous_head_root:
                raise J07Error("head root did not change at switch")
            if self.current_snapshot_root == self.previous_snapshot_root:
                raise J07Error("snapshot root did not change at switch")
            expected_authority = _derive(
                "zenodex/fcis/m6/j07/authority-state",
                {
                    "previous_authority_state_root": self.previous_authority_state_root,
                    "target_profile_root": self.target_profile_root,
                    "epoch_index": self.epoch_index,
                    "phase": self.phase.value,
                    "gate_root": self.gate_root,
                    "migration_token_root": self.migration_token_root,
                    "activation_sequence": self.activation_sequence,
                },
            )
            if self.authority_state_root != expected_authority:
                raise J07Error("post authority root is not canonically derived")
            expected_snapshot = _derive(
                "zenodex/fcis/m6/j07/snapshot",
                {
                    "previous_snapshot_root": self.previous_snapshot_root,
                    "authority_state_root": self.authority_state_root,
                    "current_state_root": self.current_state_root,
                    "deployment_config_root": self.deployment_config_root,
                    "phase": self.phase.value,
                    "gate_root": self.gate_root,
                    "activation_sequence": self.activation_sequence,
                },
            )
            if self.current_snapshot_root != expected_snapshot:
                raise J07Error("post snapshot root is not canonically derived")
            expected_head = _derive(
                "zenodex/fcis/m6/j07/head",
                {
                    "previous_head_root": self.previous_head_root,
                    "current_snapshot_root": self.current_snapshot_root,
                    "current_state_root": self.current_state_root,
                    "authority_state_root": self.authority_state_root,
                    "epoch_index": self.epoch_index,
                    "active_profile_root": self.active_profile_root,
                },
            )
            if self.current_head_root != expected_head:
                raise J07Error("post head root is not canonically derived")
        else:
            raise J07Error("kind is outside the closed enum")
        if self.context_root != _context_root(self):
            raise J07Error("context_root does not rederive")


_J07_CONTEXTS_V1: WeakValueDictionary[int, J07AuthorityContextV1] = WeakValueDictionary()
_J07_CONTEXT_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _context_snapshot(context: J07AuthorityContextV1) -> tuple[object, ...]:
    return tuple(_context_body(context).items())


def _register_context_v1(context: J07AuthorityContextV1) -> J07AuthorityContextV1:
    identity = id(context)
    _J07_CONTEXTS_V1[identity] = context
    _J07_CONTEXT_SNAPSHOTS_V1[identity] = _context_snapshot(context)
    return context


def is_verified_authority_context_v1(value: object) -> bool:
    """Check verifier provenance and unchanged fields at point of use."""

    if type(value) is not J07AuthorityContextV1:
        return False
    context = value
    if _J07_CONTEXTS_V1.get(id(context)) is not context:
        return False
    try:
        context._validate_fields()
        return _J07_CONTEXT_SNAPSHOTS_V1.get(id(context)) == _context_snapshot(context)
    except (AttributeError, J07Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def _pre_context_v1(
    gate: J06QuiescenceGateV1,
    migration_token: F06AuthorizationTokenV1,
) -> J07AuthorityContextV1:
    head = migration_token.head
    values: dict[str, object] = {
        "kind": J07StateKindV1.PRE_QUIESCED,
        "phase": dra.MigrationPhaseV1.QUIESCED,
        "epoch_index": gate.authority_epoch_index,
        "legacy_profile_root": gate.legacy_profile_root,
        "target_profile_root": gate.target_profile_root,
        "active_profile_root": gate.legacy_profile_root,
        "allowed_writer_roots": (),
        "authority_state_root": gate.authority_state_root,
        "current_head_root": gate.current_head_root,
        "current_snapshot_root": gate.current_snapshot_root,
        "current_state_root": _strip_f06_root(head.current_state_root, "current_state_root"),
        "deployment_config_root": _strip_f06_root(
            head.deployment_config_root, "deployment_config_root"
        ),
        "previous_epoch_index": gate.authority_epoch_index,
        "previous_authority_state_root": gate.authority_state_root,
        "previous_head_root": gate.current_head_root,
        "previous_snapshot_root": gate.current_snapshot_root,
        "previous_state_root": _strip_f06_root(head.current_state_root, "current_state_root"),
        "previous_deployment_config_root": _strip_f06_root(
            head.deployment_config_root, "deployment_config_root"
        ),
        "gate_root": gate.quiescence_root,
        "migration_token_root": _strip_f06_root(migration_token.token_root, "migration_token_root"),
        "activation_sequence": gate.activation_sequence,
    }
    return _register_context_v1(_context_from_values(values))


def _post_context_v1(
    pre: J07AuthorityContextV1,
) -> J07AuthorityContextV1:
    expected_epoch = pre.epoch_index + 1
    if expected_epoch > MAX_J07_SEQUENCE_V1:
        raise J07Error("authority epoch would overflow")
    authority_root = _derive(
        "zenodex/fcis/m6/j07/authority-state",
        {
            "previous_authority_state_root": pre.authority_state_root,
            "target_profile_root": pre.target_profile_root,
            "epoch_index": expected_epoch,
            "phase": dra.MigrationPhaseV1.AUTHORITY_SWITCH.value,
            "gate_root": pre.gate_root,
            "migration_token_root": pre.migration_token_root,
            "activation_sequence": pre.activation_sequence,
        },
    )
    snapshot_root = _derive(
        "zenodex/fcis/m6/j07/snapshot",
        {
            "previous_snapshot_root": pre.current_snapshot_root,
            "authority_state_root": authority_root,
            "current_state_root": pre.current_state_root,
            "deployment_config_root": pre.deployment_config_root,
            "phase": dra.MigrationPhaseV1.AUTHORITY_SWITCH.value,
            "gate_root": pre.gate_root,
            "activation_sequence": pre.activation_sequence,
        },
    )
    head_root = _derive(
        "zenodex/fcis/m6/j07/head",
        {
            "previous_head_root": pre.current_head_root,
            "current_snapshot_root": snapshot_root,
            "current_state_root": pre.current_state_root,
            "authority_state_root": authority_root,
            "epoch_index": expected_epoch,
            "active_profile_root": pre.target_profile_root,
        },
    )
    values: dict[str, object] = {
        "kind": J07StateKindV1.POST_AUTHORITY_SWITCH,
        "phase": dra.MigrationPhaseV1.AUTHORITY_SWITCH,
        "epoch_index": expected_epoch,
        "legacy_profile_root": pre.legacy_profile_root,
        "target_profile_root": pre.target_profile_root,
        "active_profile_root": pre.target_profile_root,
        "allowed_writer_roots": (pre.target_profile_root,),
        "authority_state_root": authority_root,
        "current_head_root": head_root,
        "current_snapshot_root": snapshot_root,
        "current_state_root": pre.current_state_root,
        "deployment_config_root": pre.deployment_config_root,
        "previous_epoch_index": pre.epoch_index,
        "previous_authority_state_root": pre.authority_state_root,
        "previous_head_root": pre.current_head_root,
        "previous_snapshot_root": pre.current_snapshot_root,
        "previous_state_root": pre.current_state_root,
        "previous_deployment_config_root": pre.deployment_config_root,
        "gate_root": pre.gate_root,
        "migration_token_root": pre.migration_token_root,
        "activation_sequence": pre.activation_sequence,
    }
    return _register_context_v1(_context_from_values(values))


@dataclass(frozen=True, slots=True, weakref_slot=True)
class J07WriterTokenV2:
    """Verifier-owned token bound to eligibility and one exact J07 context."""

    context_root: str
    eligibility_receipt_root: str
    promotion_subject_root: str
    eligibility_policy_root: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    expected_head_root: str
    expected_snapshot_root: str
    migration_token_root: str
    token_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J07_TOKEN_CONSTRUCTION_TOKEN_V2:
            raise J07Error("writer-token construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        for name in (
            "context_root",
            "eligibility_receipt_root",
            "promotion_subject_root",
            "eligibility_policy_root",
            "writer_profile_root",
            "authority_state_root",
            "expected_head_root",
            "expected_snapshot_root",
            "migration_token_root",
            "token_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _u32(self.authority_epoch_index, "authority_epoch_index")
        if self.token_root != writer_token_root_v2(self):
            raise J07Error("token_root does not rederive")


def writer_token_body_v2(token: J07WriterTokenV2) -> dict[str, object]:
    if type(token) is not J07WriterTokenV2:
        raise J07Error("token has the wrong exact type")
    return {
        "schema": FCIS_M6_J07_TOKEN_SCHEMA_V2,
        "context_root": token.context_root,
        "eligibility_receipt_root": token.eligibility_receipt_root,
        "promotion_subject_root": token.promotion_subject_root,
        "eligibility_policy_root": token.eligibility_policy_root,
        "writer_profile_root": token.writer_profile_root,
        "authority_epoch_index": token.authority_epoch_index,
        "authority_state_root": token.authority_state_root,
        "expected_head_root": token.expected_head_root,
        "expected_snapshot_root": token.expected_snapshot_root,
        "migration_token_root": token.migration_token_root,
    }


def writer_token_root_v2(token: J07WriterTokenV2) -> str:
    return _derive("zenodex/fcis/m6/j07/writer-token/v2", writer_token_body_v2(token))


_J07_TOKENS_V2: WeakValueDictionary[int, J07WriterTokenV2] = WeakValueDictionary()
_J07_TOKEN_SNAPSHOTS_V2: dict[int, tuple[object, ...]] = {}


def _token_snapshot_v2(token: J07WriterTokenV2) -> tuple[object, ...]:
    return (
        token.context_root,
        token.eligibility_receipt_root,
        token.promotion_subject_root,
        token.eligibility_policy_root,
        token.writer_profile_root,
        token.authority_epoch_index,
        token.authority_state_root,
        token.expected_head_root,
        token.expected_snapshot_root,
        token.migration_token_root,
        token.token_root,
    )


def _register_token_v2(token: J07WriterTokenV2) -> J07WriterTokenV2:
    identity = id(token)
    _J07_TOKENS_V2[identity] = token
    _J07_TOKEN_SNAPSHOTS_V2[identity] = _token_snapshot_v2(token)
    return token


def is_verified_writer_token_v2(value: object) -> bool:
    if type(value) is not J07WriterTokenV2:
        return False
    token = value
    if _J07_TOKENS_V2.get(id(token)) is not token:
        return False
    try:
        token._validate_fields()
        return _J07_TOKEN_SNAPSHOTS_V2.get(id(token)) == _token_snapshot_v2(token)
    except (AttributeError, J07Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def _mint_writer_token_v1(
    _context: J07AuthorityContextV1,
    _writer_profile_root: str,
) -> NoReturn:
    """Retain the minimized V1 bypass as a fail-closed compatibility tombstone."""

    raise J07Error("writer-profile eligibility receipt is required; V1 minting is closed")


def _eligibility_context_mismatch(
    context: J07AuthorityContextV1,
    receipt: WriterProfileEligibilityReceiptV1,
) -> tuple[str, ...] | None:
    claim = receipt.claim
    comparisons = (
        ("context", claim.authority_context_root, context.context_root),
        ("state", claim.current_state_root, context.current_state_root),
        ("deployment", claim.deployment_config_root, context.deployment_config_root),
        ("epoch", claim.authority_epoch, context.epoch_index),
        ("authority", claim.authority_state_root, context.authority_state_root),
        ("head", claim.expected_head_root, context.current_head_root),
        ("snapshot", claim.expected_snapshot_root, context.current_snapshot_root),
    )
    for name, observed, expected in comparisons:
        if observed != expected:
            return ("eligibility", name)
    return None


def issue_writer_token_v2(
    context: object,
    eligibility_receipt: object,
) -> J07WriterTokenV2 | J07WriterRejectV1:
    """Issue a token only from verified eligibility bound to current J07 state."""

    if not is_verified_authority_context_v1(context):
        return J07WriterRejectV1(J07RejectCodeV1.CONTEXT_REJECTED, ("context",))
    exact_context = cast(J07AuthorityContextV1, context)
    if not is_verified_writer_profile_eligibility_receipt_v1(eligibility_receipt):
        return J07WriterRejectV1(
            J07RejectCodeV1.ELIGIBILITY_REJECTED,
            ("eligibility",),
        )
    exact_receipt = cast(WriterProfileEligibilityReceiptV1, eligibility_receipt)
    mismatch = _eligibility_context_mismatch(exact_context, exact_receipt)
    if mismatch is not None:
        return J07WriterRejectV1(J07RejectCodeV1.ELIGIBILITY_CONTEXT_MISMATCH, mismatch)
    claim = exact_receipt.claim
    if claim.writer_profile_root not in exact_context.allowed_writer_roots:
        return J07WriterRejectV1(
            J07RejectCodeV1.WRITER_PROFILE_DISABLED,
            ("eligibility", "writer_profile"),
        )
    body = {
        "schema": FCIS_M6_J07_TOKEN_SCHEMA_V2,
        "context_root": exact_context.context_root,
        "eligibility_receipt_root": exact_receipt.receipt_root,
        "promotion_subject_root": claim.promotion_subject_root,
        "eligibility_policy_root": claim.eligibility_policy_root,
        "writer_profile_root": claim.writer_profile_root,
        "authority_epoch_index": exact_context.epoch_index,
        "authority_state_root": exact_context.authority_state_root,
        "expected_head_root": exact_context.current_head_root,
        "expected_snapshot_root": exact_context.current_snapshot_root,
        "migration_token_root": exact_context.migration_token_root,
    }
    return _register_token_v2(
        J07WriterTokenV2(
            context_root=exact_context.context_root,
            eligibility_receipt_root=exact_receipt.receipt_root,
            promotion_subject_root=claim.promotion_subject_root,
            eligibility_policy_root=claim.eligibility_policy_root,
            writer_profile_root=claim.writer_profile_root,
            authority_epoch_index=exact_context.epoch_index,
            authority_state_root=exact_context.authority_state_root,
            expected_head_root=exact_context.current_head_root,
            expected_snapshot_root=exact_context.current_snapshot_root,
            migration_token_root=exact_context.migration_token_root,
            token_root=_derive("zenodex/fcis/m6/j07/writer-token/v2", body),
            _construction_token=_J07_TOKEN_CONSTRUCTION_TOKEN_V2,
        )
    )


@dataclass(frozen=True, slots=True)
class J07WriterRejectV1:
    """Typed state-preserving writer rejection."""

    code: J07RejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not J07RejectCodeV1:
            raise J07Error("writer rejection code has the wrong exact type")
        _path(self.path, "writer rejection path")


J07WriterTokenIssueV2: TypeAlias = J07WriterTokenV2 | J07WriterRejectV1


@dataclass(frozen=True, slots=True)
class J07WriterAcceptedV2:
    """Verifier-owned accepted writer observation; it carries no authority."""

    context_root: str
    token_root: str
    eligibility_receipt_root: str
    promotion_subject_root: str
    eligibility_policy_root: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    head_root: str
    snapshot_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J07_DECISION_CONSTRUCTION_TOKEN_V1:
            raise J07Error("accepted writer decision construction is verifier-owned")
        _digest(self.context_root, "context_root")
        _digest(self.token_root, "token_root")
        _digest(self.eligibility_receipt_root, "eligibility_receipt_root")
        _digest(self.promotion_subject_root, "promotion_subject_root")
        _digest(self.eligibility_policy_root, "eligibility_policy_root")
        _digest(self.writer_profile_root, "writer_profile_root")
        _u32(self.authority_epoch_index, "authority_epoch_index")
        _digest(self.authority_state_root, "authority_state_root")
        _digest(self.head_root, "head_root")
        _digest(self.snapshot_root, "snapshot_root")


J07WriterDecisionV2: TypeAlias = J07WriterAcceptedV2 | J07WriterRejectV1


def authorize_writer_v2(
    context: object,
    token: object,
    eligibility_receipt: object,
) -> J07WriterDecisionV2:
    """Admit a writer after fresh token, eligibility, and context validation."""

    if not is_verified_authority_context_v1(context):
        return J07WriterRejectV1(J07RejectCodeV1.CONTEXT_REJECTED, ("context",))
    exact_context = cast(J07AuthorityContextV1, context)
    if not is_verified_writer_token_v2(token):
        return J07WriterRejectV1(J07RejectCodeV1.TOKEN_REJECTED, ("token",))
    exact_token = cast(J07WriterTokenV2, token)
    if not is_verified_writer_profile_eligibility_receipt_v1(eligibility_receipt):
        return J07WriterRejectV1(
            J07RejectCodeV1.ELIGIBILITY_REJECTED,
            ("eligibility",),
        )
    exact_receipt = cast(WriterProfileEligibilityReceiptV1, eligibility_receipt)
    claim = exact_receipt.claim
    eligibility_token_fields = (
        ("receipt", exact_token.eligibility_receipt_root, exact_receipt.receipt_root),
        ("promotion", exact_token.promotion_subject_root, claim.promotion_subject_root),
        ("policy", exact_token.eligibility_policy_root, claim.eligibility_policy_root),
        ("writer_profile", exact_token.writer_profile_root, claim.writer_profile_root),
    )
    for name, observed, expected in eligibility_token_fields:
        if observed != expected:
            return J07WriterRejectV1(
                J07RejectCodeV1.ELIGIBILITY_CONTEXT_MISMATCH,
                ("token", "eligibility", name),
            )
    if exact_token.context_root != exact_context.context_root:
        return J07WriterRejectV1(J07RejectCodeV1.STALE_TOKEN, ("token", "context"))
    if exact_token.authority_epoch_index != exact_context.epoch_index:
        return J07WriterRejectV1(J07RejectCodeV1.STALE_TOKEN, ("token", "epoch"))
    if exact_token.authority_state_root != exact_context.authority_state_root:
        return J07WriterRejectV1(J07RejectCodeV1.STALE_TOKEN, ("token", "authority"))
    if exact_token.expected_head_root != exact_context.current_head_root:
        return J07WriterRejectV1(J07RejectCodeV1.STALE_TOKEN, ("token", "head"))
    if exact_token.expected_snapshot_root != exact_context.current_snapshot_root:
        return J07WriterRejectV1(J07RejectCodeV1.STALE_TOKEN, ("token", "snapshot"))
    if exact_token.migration_token_root != exact_context.migration_token_root:
        return J07WriterRejectV1(J07RejectCodeV1.STALE_TOKEN, ("token", "migration"))
    mismatch = _eligibility_context_mismatch(exact_context, exact_receipt)
    if mismatch is not None:
        return J07WriterRejectV1(J07RejectCodeV1.ELIGIBILITY_CONTEXT_MISMATCH, mismatch)
    if exact_token.writer_profile_root not in exact_context.allowed_writer_roots:
        return J07WriterRejectV1(
            J07RejectCodeV1.WRITER_PROFILE_DISABLED,
            ("token", "writer_profile"),
        )
    return J07WriterAcceptedV2(
        context_root=exact_context.context_root,
        token_root=exact_token.token_root,
        eligibility_receipt_root=exact_receipt.receipt_root,
        promotion_subject_root=claim.promotion_subject_root,
        eligibility_policy_root=claim.eligibility_policy_root,
        writer_profile_root=exact_token.writer_profile_root,
        authority_epoch_index=exact_context.epoch_index,
        authority_state_root=exact_context.authority_state_root,
        head_root=exact_context.current_head_root,
        snapshot_root=exact_context.current_snapshot_root,
        _construction_token=_J07_DECISION_CONSTRUCTION_TOKEN_V1,
    )


def _switch_root(
    gate_root: str,
    migration_token_root: str,
    pre_context_root: str,
    post_context_root: str,
) -> str:
    return _derive(
        "zenodex/fcis/m6/j07/switch",
        {
            "schema": FCIS_M6_J07_SWITCH_SCHEMA_V1,
            "gate_root": gate_root,
            "migration_token_root": migration_token_root,
            "pre_context_root": pre_context_root,
            "post_context_root": post_context_root,
        },
    )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class J07SwitchSuccessV1:
    """Verifier-owned complete pre/post switch atom."""

    gate_root: str
    migration_token_root: str
    pre_context: J07AuthorityContextV1
    post_context: J07AuthorityContextV1
    switch_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J07_SWITCH_CONSTRUCTION_TOKEN_V1:
            raise J07Error("switch-result construction is verifier-owned")
        _digest(self.gate_root, "gate_root")
        _digest(self.migration_token_root, "migration_token_root")
        if not is_verified_authority_context_v1(self.pre_context):
            raise J07Error("pre context lacks verifier provenance")
        if not is_verified_authority_context_v1(self.post_context):
            raise J07Error("post context lacks verifier provenance")
        if self.pre_context.kind is not J07StateKindV1.PRE_QUIESCED:
            raise J07Error("switch pre context has the wrong kind")
        if self.post_context.kind is not J07StateKindV1.POST_AUTHORITY_SWITCH:
            raise J07Error("switch post context has the wrong kind")
        if self.pre_context.gate_root != self.gate_root:
            raise J07Error("switch gate root is not bound to pre context")
        if self.pre_context.migration_token_root != self.migration_token_root:
            raise J07Error("switch token root is not bound to pre context")
        if self.post_context.gate_root != self.gate_root:
            raise J07Error("switch gate root is not bound to post context")
        if self.post_context.migration_token_root != self.migration_token_root:
            raise J07Error("switch token root is not bound to post context")
        if self.post_context.legacy_profile_root != self.pre_context.legacy_profile_root:
            raise J07Error("switch changed the legacy profile identity")
        if self.post_context.target_profile_root != self.pre_context.target_profile_root:
            raise J07Error("switch changed the target profile identity")
        if self.post_context.previous_epoch_index != self.pre_context.epoch_index:
            raise J07Error("switch successor does not name the predecessor epoch")
        if self.post_context.previous_authority_state_root != self.pre_context.authority_state_root:
            raise J07Error("switch successor does not name the predecessor authority")
        if self.post_context.previous_head_root != self.pre_context.current_head_root:
            raise J07Error("switch successor does not name the predecessor head")
        if self.post_context.previous_snapshot_root != self.pre_context.current_snapshot_root:
            raise J07Error("switch successor does not name the predecessor snapshot")
        if self.post_context.previous_state_root != self.pre_context.current_state_root:
            raise J07Error("switch successor does not name the predecessor state")
        if (
            self.post_context.previous_deployment_config_root
            != self.pre_context.deployment_config_root
        ):
            raise J07Error("switch successor does not name the predecessor deployment")
        if self.switch_root != _switch_root(
            self.gate_root,
            self.migration_token_root,
            self.pre_context.context_root,
            self.post_context.context_root,
        ):
            raise J07Error("switch_root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__(_J07_SWITCH_CONSTRUCTION_TOKEN_V1)
        return {
            "schema": FCIS_M6_J07_SWITCH_SCHEMA_V1,
            "gate_root": self.gate_root,
            "migration_token_root": self.migration_token_root,
            "pre_context_root": self.pre_context.context_root,
            "post_context_root": self.post_context.context_root,
            "pre_phase": self.pre_context.phase.value,
            "post_phase": self.post_context.phase.value,
            "pre_epoch_index": self.pre_context.epoch_index,
            "post_epoch_index": self.post_context.epoch_index,
            "pre_authority_state_root": self.pre_context.authority_state_root,
            "post_authority_state_root": self.post_context.authority_state_root,
            "pre_head_root": self.pre_context.current_head_root,
            "post_head_root": self.post_context.current_head_root,
            "pre_snapshot_root": self.pre_context.current_snapshot_root,
            "post_snapshot_root": self.post_context.current_snapshot_root,
            "post_active_profile_root": self.post_context.active_profile_root,
            "post_allowed_writer_roots": list(self.post_context.allowed_writer_roots),
            "switch_root": self.switch_root,
        }


@dataclass(frozen=True, slots=True)
class J07SwitchRejectV1:
    """Typed switch rejection with no successor context."""

    code: J07RejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not J07RejectCodeV1:
            raise J07Error("switch rejection code has the wrong exact type")
        _path(self.path, "switch rejection path")


J07SwitchResultV1: TypeAlias = J07SwitchSuccessV1 | J07SwitchRejectV1


def switch_authority_v1(
    gate: object,
    reopened: object,
    *,
    genesis: object,
    migration_token: object,
    verifier_adapter: object,
    current_epoch: object,
) -> J07SwitchResultV1:
    """Perform one complete verifier-gated authority-switch relation."""

    if not is_verified_quiescence_gate_v1(gate):
        return J07SwitchRejectV1(J07RejectCodeV1.GATE_REJECTED, ("gate",))
    exact_gate = cast(J06QuiescenceGateV1, gate)
    if exact_gate.phase is not dra.MigrationPhaseV1.QUIESCED:
        return J07SwitchRejectV1(J07RejectCodeV1.GATE_PHASE_REJECTED, ("gate", "phase"))
    if type(migration_token) is not F06AuthorizationTokenV1:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", "exact_type"),
        )
    exact_token = cast(F06AuthorizationTokenV1, migration_token)
    try:
        exact_token.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", "integrity"),
        )
    use = require_f06_token_at_use(
        reopened,
        genesis=genesis,
        token=exact_token,
        operation=F06OperationV1.MIGRATION,
        verifier_adapter=verifier_adapter,
        current_epoch=current_epoch,
    )
    if type(use) is F06AuthorizationRejectV1:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", use.code.value),
        )
    if type(use) is not F06AuthorizationUseV1:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", "wrong_use_type"),
        )
    try:
        use.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", "use_integrity"),
        )
    if use.operation is not F06OperationV1.MIGRATION or use.token_root != exact_token.token_root:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", "use_binding"),
        )
    try:
        head_root = _strip_f06_root(exact_token.head.head_root, "head_root")
        snapshot_root = _strip_f06_root(exact_token.head.snapshot_root, "snapshot_root")
        authority_root = _strip_f06_root(
            exact_token.head.authority_state_root, "authority_state_root"
        )
    except (J07Error, TypeError, ValueError, ArithmeticError):
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", "head_integrity"),
        )
    if use.head_root != exact_token.head.head_root:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_REJECTED,
            ("migration_token", "head_binding"),
        )
    if head_root != exact_gate.current_head_root:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_HEAD_MISMATCH,
            ("migration_token", "head"),
        )
    if snapshot_root != exact_gate.current_snapshot_root:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_SNAPSHOT_MISMATCH,
            ("migration_token", "snapshot"),
        )
    if authority_root != exact_gate.authority_state_root:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_AUTHORITY_MISMATCH,
            ("migration_token", "authority"),
        )
    if exact_token.head.authority_epoch != exact_gate.authority_epoch_index:
        return J07SwitchRejectV1(
            J07RejectCodeV1.AUTHORIZATION_EPOCH_MISMATCH,
            ("migration_token", "epoch"),
        )
    if exact_gate.legacy_profile_root == exact_gate.target_profile_root:
        return J07SwitchRejectV1(J07RejectCodeV1.PROFILE_COLLISION, ("gate", "profiles"))
    try:
        pre = _pre_context_v1(exact_gate, exact_token)
        post = _post_context_v1(pre)
        return J07SwitchSuccessV1(
            gate_root=exact_gate.quiescence_root,
            migration_token_root=pre.migration_token_root,
            pre_context=pre,
            post_context=post,
            switch_root=_switch_root(
                exact_gate.quiescence_root,
                pre.migration_token_root,
                pre.context_root,
                post.context_root,
            ),
            _construction_token=_J07_SWITCH_CONSTRUCTION_TOKEN_V1,
        )
    except (AttributeError, J07Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return J07SwitchRejectV1(J07RejectCodeV1.CONTEXT_REJECTED, ("switch", "context"))


__all__ = (
    "FCIS_M6_J07_CONTEXT_SCHEMA_V1",
    "FCIS_M6_J07_SCHEMA_V1",
    "FCIS_M6_J07_SWITCH_SCHEMA_V1",
    "FCIS_M6_J07_TOKEN_SCHEMA_V1",
    "FCIS_M6_J07_TOKEN_SCHEMA_V2",
    "J07AuthorityContextV1",
    "J07Error",
    "J07RejectCodeV1",
    "J07StateKindV1",
    "J07SwitchRejectV1",
    "J07SwitchResultV1",
    "J07SwitchSuccessV1",
    "J07WriterAcceptedV2",
    "J07WriterDecisionV2",
    "J07WriterRejectV1",
    "J07WriterTokenIssueV2",
    "J07WriterTokenV2",
    "authorize_writer_v2",
    "issue_writer_token_v2",
    "is_verified_authority_context_v1",
    "is_verified_writer_token_v2",
    "switch_authority_v1",
    "writer_token_body_v2",
    "writer_token_root_v2",
)
