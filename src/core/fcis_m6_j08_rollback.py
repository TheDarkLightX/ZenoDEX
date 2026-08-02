"""Typed FCIS M6 J08 rollback without history erasure.

J08 consumes the verifier-owned J07 authority-switch atom and two complete
state witnesses.  It emits one compensating rollback certificate that restores
the predecessor's state, configuration, residual, nullifier, outbox, and
effect-identity roots while appending a rollback commitment to history and
advancing the authority epoch.  The relation is a deterministic research
model.  It does not delete rows, authorize a datastore transaction, or mount a
runtime rollback path.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, TypeAlias, cast
from weakref import WeakValueDictionary

from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_j07_authority_switch import J07SwitchSuccessV1
from src.state.canonical import canonical_json_bytes

FCIS_M6_J08_SCHEMA_V1: Final = "zenodex/fcis/m6/j08/rollback/v1"
FCIS_M6_J08_STATE_SCHEMA_V1: Final = "zenodex/fcis/m6/j08/complete-state/v1"
FCIS_M6_J08_CERTIFICATE_SCHEMA_V1: Final = "zenodex/fcis/m6/j08/rollback-certificate/v1"
MAX_J08_SEQUENCE_V1: Final = (1 << 32) - 1
MAX_J08_PATH_PARTS_V1: Final = 8

_J08_STATE_CONSTRUCTION_TOKEN_V1 = object()
_J08_CERTIFICATE_CONSTRUCTION_TOKEN_V1 = object()
_J08_SUCCESS_CONSTRUCTION_TOKEN_V1 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")


class J08Error(ValueError):
    """Raised when a J08 value is outside its closed research language."""


class J08RollbackReasonV1(str, Enum):
    """The closed v1 reason for a compensating rollback."""

    POST_SWITCH_VALIDATION_FAILURE = "post_switch_validation_failure"


class J08RollbackCodeV1(str, Enum):
    """Typed rejection classes for rollback construction and use."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    SWITCH_REJECTED = "switch_rejected"
    SOURCE_STATE_REJECTED = "source_state_rejected"
    ANCHOR_STATE_REJECTED = "anchor_state_rejected"
    REASON_REJECTED = "reason_rejected"
    SEQUENCE_REJECTED = "sequence_rejected"
    SOURCE_SWITCH_MISMATCH = "source_switch_mismatch"
    ANCHOR_SWITCH_MISMATCH = "anchor_switch_mismatch"
    COMPLETE_STATE_MISMATCH = "complete_state_mismatch"
    STATE_NOT_PRESERVED = "state_not_preserved"
    CONFIG_NOT_PRESERVED = "config_not_preserved"
    RESIDUAL_NOT_PRESERVED = "residual_not_preserved"
    NULLIFIER_NOT_PRESERVED = "nullifier_not_preserved"
    OUTBOX_NOT_PRESERVED = "outbox_not_preserved"
    EFFECT_IDENTITY_NOT_PRESERVED = "effect_identity_not_preserved"
    HISTORY_ERASED = "history_erased"
    TARGET_MISMATCH = "target_mismatch"
    CERTIFICATE_MISMATCH = "certificate_mismatch"


def _text(value: object, name: str, *, maximum_bytes: int = 256) -> str:
    if type(value) is not str or not value:
        raise J08Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise J08Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise J08Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise J08Error(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in _HEX_DIGITS for character in checked):
        raise J08Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    minimum = 1 if positive else 0
    if type(value) is not int or value < minimum or value > MAX_J08_SEQUENCE_V1:
        raise J08Error(f"{name} is outside its closed u32 bound")
    return value


def _path(value: object, name: str) -> tuple[str, ...]:
    if type(value) is not tuple or not value:
        raise J08Error(f"{name} must be a nonempty exact tuple")
    if len(value) > MAX_J08_PATH_PARTS_V1:
        raise J08Error(f"{name} exceeds its closed collection bound")
    return tuple(
        _text(item, f"{name}[{index}]", maximum_bytes=64) for index, item in enumerate(value)
    )


def _derive(domain: str, payload: dict[str, object]) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(payload)).hexdigest()


def _state_body(state: "J08CompleteStateV1") -> dict[str, object]:
    return {
        "schema": FCIS_M6_J08_STATE_SCHEMA_V1,
        "phase": state.phase.value,
        "authority_epoch_index": state.authority_epoch_index,
        "allowed_writer_roots": list(state.allowed_writer_roots),
        "active_profile_root": state.active_profile_root,
        "authority_state_root": state.authority_state_root,
        "context_snapshot_root": state.context_snapshot_root,
        "current_state_root": state.current_state_root,
        "deployment_config_root": state.deployment_config_root,
        "history_root": state.history_root,
        "residual_state_root": state.residual_state_root,
        "nullifier_root": state.nullifier_root,
        "outbox_root": state.outbox_root,
        "effect_identity_root": state.effect_identity_root,
    }


def _state_root(state: "J08CompleteStateV1") -> str:
    return _derive("zenodex/fcis/m6/j08/complete-snapshot", _state_body(state))


@dataclass(frozen=True, slots=True, weakref_slot=True)
class J08CompleteStateV1:
    """Verifier-owned complete state aggregate used by rollback."""

    phase: dra.MigrationPhaseV1
    authority_epoch_index: int
    allowed_writer_roots: tuple[str, ...]
    active_profile_root: str
    authority_state_root: str
    context_snapshot_root: str
    current_state_root: str
    deployment_config_root: str
    history_root: str
    residual_state_root: str
    nullifier_root: str
    outbox_root: str
    effect_identity_root: str
    snapshot_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J08_STATE_CONSTRUCTION_TOKEN_V1:
            raise J08Error("complete-state construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        if type(self.phase) is not dra.MigrationPhaseV1:
            raise J08Error("phase has the wrong exact type")
        _u32(self.authority_epoch_index, "authority_epoch_index")
        if type(self.allowed_writer_roots) is not tuple:
            raise J08Error("allowed_writer_roots must be an exact tuple")
        if len(self.allowed_writer_roots) > 1:
            raise J08Error("J08 permits at most one active writer profile")
        for index, writer in enumerate(self.allowed_writer_roots):
            _digest(writer, f"allowed_writer_roots[{index}]")
        for name in (
            "active_profile_root",
            "authority_state_root",
            "context_snapshot_root",
            "current_state_root",
            "deployment_config_root",
            "history_root",
            "residual_state_root",
            "nullifier_root",
            "outbox_root",
            "effect_identity_root",
            "snapshot_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        if self.snapshot_root != _state_root(self):
            raise J08Error("snapshot_root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {**_state_body(self), "snapshot_root": self.snapshot_root}


_J08_STATES_V1: WeakValueDictionary[int, J08CompleteStateV1] = WeakValueDictionary()
_J08_STATE_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _state_snapshot(state: J08CompleteStateV1) -> tuple[object, ...]:
    return tuple(_state_body(state).items()) + (state.snapshot_root,)


def _register_state_v1(state: J08CompleteStateV1) -> J08CompleteStateV1:
    identity = id(state)
    _J08_STATES_V1[identity] = state
    _J08_STATE_SNAPSHOTS_V1[identity] = _state_snapshot(state)
    return state


def is_verified_complete_state_v1(value: object) -> bool:
    """Check provenance and unchanged fields for a complete state witness."""

    if type(value) is not J08CompleteStateV1:
        return False
    state = value
    if _J08_STATES_V1.get(id(state)) is not state:
        return False
    try:
        state._validate_fields()
        return _J08_STATE_SNAPSHOTS_V1.get(id(state)) == _state_snapshot(state)
    except (AttributeError, J08Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def _state_from_values(values: dict[str, object]) -> J08CompleteStateV1:
    body = {
        "schema": FCIS_M6_J08_STATE_SCHEMA_V1,
        "phase": cast(dra.MigrationPhaseV1, values["phase"]).value,
        "authority_epoch_index": values["authority_epoch_index"],
        "allowed_writer_roots": list(cast(tuple[str, ...], values["allowed_writer_roots"])),
        "active_profile_root": values["active_profile_root"],
        "authority_state_root": values["authority_state_root"],
        "context_snapshot_root": values["context_snapshot_root"],
        "current_state_root": values["current_state_root"],
        "deployment_config_root": values["deployment_config_root"],
        "history_root": values["history_root"],
        "residual_state_root": values["residual_state_root"],
        "nullifier_root": values["nullifier_root"],
        "outbox_root": values["outbox_root"],
        "effect_identity_root": values["effect_identity_root"],
    }
    state = J08CompleteStateV1(
        phase=cast(dra.MigrationPhaseV1, values["phase"]),
        authority_epoch_index=cast(int, values["authority_epoch_index"]),
        allowed_writer_roots=cast(tuple[str, ...], values["allowed_writer_roots"]),
        active_profile_root=cast(str, values["active_profile_root"]),
        authority_state_root=cast(str, values["authority_state_root"]),
        context_snapshot_root=cast(str, values["context_snapshot_root"]),
        current_state_root=cast(str, values["current_state_root"]),
        deployment_config_root=cast(str, values["deployment_config_root"]),
        history_root=cast(str, values["history_root"]),
        residual_state_root=cast(str, values["residual_state_root"]),
        nullifier_root=cast(str, values["nullifier_root"]),
        outbox_root=cast(str, values["outbox_root"]),
        effect_identity_root=cast(str, values["effect_identity_root"]),
        snapshot_root=_derive("zenodex/fcis/m6/j08/complete-snapshot", body),
        _construction_token=_J08_STATE_CONSTRUCTION_TOKEN_V1,
    )
    return _register_state_v1(state)


def _rollback_history_root(
    source: J08CompleteStateV1,
    anchor: J08CompleteStateV1,
    switch: J07SwitchSuccessV1,
    reason: J08RollbackReasonV1,
    rollback_sequence: int,
) -> str:
    return _derive(
        "zenodex/fcis/m6/j08/rollback-history",
        {
            "schema": FCIS_M6_J08_SCHEMA_V1,
            "anchor_history_root": anchor.history_root,
            "source_history_root": source.history_root,
            "switch_root": switch.switch_root,
            "reason": reason.value,
            "rollback_sequence": rollback_sequence,
        },
    )


def _rollback_target_values(
    source: J08CompleteStateV1,
    anchor: J08CompleteStateV1,
    switch: J07SwitchSuccessV1,
    reason: J08RollbackReasonV1,
    rollback_sequence: int,
) -> dict[str, object]:
    history_root = _rollback_history_root(source, anchor, switch, reason, rollback_sequence)
    authority_root = _derive(
        "zenodex/fcis/m6/j08/rollback-authority",
        {
            "schema": FCIS_M6_J08_SCHEMA_V1,
            "source_authority_state_root": source.authority_state_root,
            "anchor_authority_state_root": anchor.authority_state_root,
            "active_profile_root": anchor.active_profile_root,
            "phase": dra.MigrationPhaseV1.POST_SWITCH_VALIDATION.value,
            "rollback_sequence": rollback_sequence,
            "history_root": history_root,
        },
    )
    context_snapshot_root = _derive(
        "zenodex/fcis/m6/j08/rollback-context",
        {
            "schema": FCIS_M6_J08_SCHEMA_V1,
            "switch_root": switch.switch_root,
            "source_context_snapshot_root": source.context_snapshot_root,
            "anchor_context_snapshot_root": anchor.context_snapshot_root,
            "authority_state_root": authority_root,
            "rollback_sequence": rollback_sequence,
        },
    )
    return {
        "phase": dra.MigrationPhaseV1.POST_SWITCH_VALIDATION,
        "authority_epoch_index": rollback_sequence,
        "allowed_writer_roots": (),
        "active_profile_root": anchor.active_profile_root,
        "authority_state_root": authority_root,
        "context_snapshot_root": context_snapshot_root,
        "current_state_root": anchor.current_state_root,
        "deployment_config_root": anchor.deployment_config_root,
        "history_root": history_root,
        "residual_state_root": anchor.residual_state_root,
        "nullifier_root": anchor.nullifier_root,
        "outbox_root": anchor.outbox_root,
        "effect_identity_root": anchor.effect_identity_root,
    }


def _rollback_root_from_values(
    switch: J07SwitchSuccessV1,
    source: J08CompleteStateV1,
    anchor: J08CompleteStateV1,
    target: J08CompleteStateV1,
    reason: J08RollbackReasonV1,
    rollback_sequence: int,
) -> str:
    return _derive(
        "zenodex/fcis/m6/j08/rollback-certificate",
        {
            "schema": FCIS_M6_J08_CERTIFICATE_SCHEMA_V1,
            "switch_root": switch.switch_root,
            "source_snapshot_root": source.snapshot_root,
            "anchor_snapshot_root": anchor.snapshot_root,
            "target_snapshot_root": target.snapshot_root,
            "reason": reason.value,
            "rollback_sequence": rollback_sequence,
        },
    )


def _rollback_root(certificate: "J08RollbackCertificateV1") -> str:
    return _rollback_root_from_values(
        certificate.switch,
        certificate.source,
        certificate.anchor,
        certificate.target,
        certificate.reason,
        certificate.rollback_sequence,
    )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class J08RollbackCertificateV1:
    """Verifier-owned complete rollback certificate."""

    switch: J07SwitchSuccessV1
    source: J08CompleteStateV1
    anchor: J08CompleteStateV1
    target: J08CompleteStateV1
    reason: J08RollbackReasonV1
    rollback_sequence: int
    rollback_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J08_CERTIFICATE_CONSTRUCTION_TOKEN_V1:
            raise J08Error("rollback-certificate construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        if type(self.switch) is not J07SwitchSuccessV1:
            raise J08Error("switch has the wrong exact type")
        try:
            self.switch.to_wire()
        except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError) as exc:
            raise J08Error("switch lacks verifier validation") from exc
        if not is_verified_complete_state_v1(self.source):
            raise J08Error("source state lacks verifier provenance")
        if not is_verified_complete_state_v1(self.anchor):
            raise J08Error("anchor state lacks verifier provenance")
        if not is_verified_complete_state_v1(self.target):
            raise J08Error("target state lacks verifier provenance")
        if type(self.reason) is not J08RollbackReasonV1:
            raise J08Error("rollback reason has the wrong exact type")
        _u32(self.rollback_sequence, "rollback_sequence", positive=True)
        if self.source.authority_epoch_index == MAX_J08_SEQUENCE_V1:
            raise J08Error("rollback authority epoch would overflow")
        if self.rollback_sequence != self.source.authority_epoch_index + 1:
            raise J08Error("rollback sequence must advance the source epoch exactly once")
        pre = self.switch.pre_context
        post = self.switch.post_context
        if (
            self.source.phase is not post.phase
            or self.source.authority_epoch_index != post.epoch_index
            or self.source.active_profile_root != post.active_profile_root
            or self.source.authority_state_root != post.authority_state_root
            or self.source.context_snapshot_root != post.current_snapshot_root
            or self.source.current_state_root != post.current_state_root
            or self.source.deployment_config_root != post.deployment_config_root
            or self.source.allowed_writer_roots != post.allowed_writer_roots
        ):
            raise J08Error("source state is not bound to the J07 post context")
        if (
            self.anchor.phase is not pre.phase
            or self.anchor.authority_epoch_index != pre.epoch_index
            or self.anchor.active_profile_root != pre.active_profile_root
            or self.anchor.authority_state_root != pre.authority_state_root
            or self.anchor.context_snapshot_root != pre.current_snapshot_root
            or self.anchor.current_state_root != pre.current_state_root
            or self.anchor.deployment_config_root != pre.deployment_config_root
            or self.anchor.allowed_writer_roots != pre.allowed_writer_roots
        ):
            raise J08Error("anchor state is not bound to the J07 pre context")
        for name in (
            "history_root",
            "residual_state_root",
            "nullifier_root",
            "outbox_root",
            "effect_identity_root",
        ):
            if getattr(self.source, name) != getattr(self.anchor, name):
                raise J08Error(f"source and anchor disagree on complete {name}")
        expected_values = _rollback_target_values(
            self.source,
            self.anchor,
            self.switch,
            self.reason,
            self.rollback_sequence,
        )
        expected_target = _state_from_values(expected_values)
        if self.target != expected_target:
            raise J08Error("rollback target is not canonically derived")
        if self.target.history_root == self.anchor.history_root:
            raise J08Error("rollback erased the history transition")
        if self.target.current_state_root != self.anchor.current_state_root:
            raise J08Error("rollback did not restore current state")
        if self.target.deployment_config_root != self.anchor.deployment_config_root:
            raise J08Error("rollback did not restore deployment configuration")
        if self.target.residual_state_root != self.anchor.residual_state_root:
            raise J08Error("rollback did not restore residual state")
        if self.target.nullifier_root != self.anchor.nullifier_root:
            raise J08Error("rollback did not restore nullifier state")
        if self.target.outbox_root != self.anchor.outbox_root:
            raise J08Error("rollback did not restore outbox identity")
        if self.target.effect_identity_root != self.anchor.effect_identity_root:
            raise J08Error("rollback did not restore effect identity")
        _digest(self.rollback_root, "rollback_root")
        if self.rollback_root != _rollback_root(self):
            raise J08Error("rollback_root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            "schema": FCIS_M6_J08_CERTIFICATE_SCHEMA_V1,
            "switch_root": self.switch.switch_root,
            "source": self.source.to_wire(),
            "anchor": self.anchor.to_wire(),
            "target": self.target.to_wire(),
            "reason": self.reason.value,
            "rollback_sequence": self.rollback_sequence,
            "rollback_root": self.rollback_root,
        }


_J08_CERTIFICATES_V1: WeakValueDictionary[int, J08RollbackCertificateV1] = WeakValueDictionary()
_J08_CERTIFICATE_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _certificate_snapshot(certificate: J08RollbackCertificateV1) -> tuple[object, ...]:
    return (
        certificate.switch.switch_root,
        certificate.source.snapshot_root,
        certificate.anchor.snapshot_root,
        certificate.target.snapshot_root,
        certificate.reason,
        certificate.rollback_sequence,
        certificate.rollback_root,
    )


def _register_certificate_v1(certificate: J08RollbackCertificateV1) -> J08RollbackCertificateV1:
    identity = id(certificate)
    _J08_CERTIFICATES_V1[identity] = certificate
    _J08_CERTIFICATE_SNAPSHOTS_V1[identity] = _certificate_snapshot(certificate)
    return certificate


def is_verified_rollback_certificate_v1(value: object) -> bool:
    """Check certificate provenance and all complete-state bindings."""

    if type(value) is not J08RollbackCertificateV1:
        return False
    certificate = value
    if _J08_CERTIFICATES_V1.get(id(certificate)) is not certificate:
        return False
    try:
        certificate._validate_fields()
        return _J08_CERTIFICATE_SNAPSHOTS_V1.get(id(certificate)) == _certificate_snapshot(
            certificate
        )
    except (AttributeError, J08Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


@dataclass(frozen=True, slots=True)
class J08RollbackSuccessV1:
    """Complete rollback observation with no implicit movement capability."""

    certificate: J08RollbackCertificateV1
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J08_SUCCESS_CONSTRUCTION_TOKEN_V1:
            raise J08Error("rollback-success construction is verifier-owned")
        if not is_verified_rollback_certificate_v1(self.certificate):
            raise J08Error("rollback certificate lacks verifier provenance")

    @property
    def requires_fresh_authorization(self) -> bool:
        return True

    @property
    def can_accept_value_movement(self) -> bool:
        return False

    def to_wire(self) -> dict[str, object]:
        self.__post_init__(_J08_SUCCESS_CONSTRUCTION_TOKEN_V1)
        return {
            "schema": FCIS_M6_J08_SCHEMA_V1,
            "certificate": self.certificate.to_wire(),
            "requires_fresh_authorization": True,
            "can_accept_value_movement": False,
        }


@dataclass(frozen=True, slots=True)
class J08RollbackRejectV1:
    """Typed rollback rejection with no successor state."""

    code: J08RollbackCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not J08RollbackCodeV1:
            raise J08Error("rollback rejection code has the wrong exact type")
        _path(self.path, "rollback rejection path")


J08RollbackResultV1: TypeAlias = J08RollbackSuccessV1 | J08RollbackRejectV1


def _reject(code: J08RollbackCodeV1, *path: str) -> J08RollbackRejectV1:
    return J08RollbackRejectV1(code, path)


def rollback_j08_v1(
    switch: object,
    source: object,
    anchor: object,
    *,
    reason: object,
    rollback_sequence: object,
) -> J08RollbackResultV1:
    """Build one verifier-gated rollback certificate from complete witnesses."""

    if type(switch) is not J07SwitchSuccessV1:
        return _reject(J08RollbackCodeV1.SWITCH_REJECTED, "switch", "exact_type")
    exact_switch = cast(J07SwitchSuccessV1, switch)
    try:
        exact_switch.to_wire()
    except (AttributeError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(J08RollbackCodeV1.SWITCH_REJECTED, "switch", "validation")
    if not is_verified_complete_state_v1(source):
        return _reject(J08RollbackCodeV1.SOURCE_STATE_REJECTED, "source")
    if not is_verified_complete_state_v1(anchor):
        return _reject(J08RollbackCodeV1.ANCHOR_STATE_REJECTED, "anchor")
    if type(reason) is not J08RollbackReasonV1:
        return _reject(J08RollbackCodeV1.REASON_REJECTED, "reason")
    if type(rollback_sequence) is not int:
        return _reject(J08RollbackCodeV1.SEQUENCE_REJECTED, "rollback_sequence", "exact_type")
    try:
        sequence = _u32(rollback_sequence, "rollback_sequence", positive=True)
    except J08Error:
        return _reject(J08RollbackCodeV1.SEQUENCE_REJECTED, "rollback_sequence")
    exact_source = cast(J08CompleteStateV1, source)
    if exact_source.authority_epoch_index == MAX_J08_SEQUENCE_V1:
        return _reject(J08RollbackCodeV1.SEQUENCE_REJECTED, "rollback_sequence", "overflow")
    if sequence != exact_source.authority_epoch_index + 1:
        return _reject(J08RollbackCodeV1.SEQUENCE_REJECTED, "rollback_sequence", "epoch")
    exact_anchor = cast(J08CompleteStateV1, anchor)
    for name in (
        "history_root",
        "residual_state_root",
        "nullifier_root",
        "outbox_root",
        "effect_identity_root",
    ):
        if getattr(exact_source, name) != getattr(exact_anchor, name):
            return _reject(J08RollbackCodeV1.COMPLETE_STATE_MISMATCH, "source", "anchor", name)
    try:
        target = _register_state_v1(
            _state_from_values(
                _rollback_target_values(
                    exact_source,
                    exact_anchor,
                    exact_switch,
                    reason,
                    sequence,
                )
            )
        )
        certificate = J08RollbackCertificateV1(
            switch=exact_switch,
            source=exact_source,
            anchor=exact_anchor,
            target=target,
            reason=reason,
            rollback_sequence=sequence,
            rollback_root=_rollback_root_from_values(
                exact_switch,
                exact_source,
                exact_anchor,
                target,
                reason,
                sequence,
            ),
            _construction_token=_J08_CERTIFICATE_CONSTRUCTION_TOKEN_V1,
        )
        certificate._validate_fields()
        _register_certificate_v1(certificate)
        return J08RollbackSuccessV1(
            certificate=certificate,
            _construction_token=_J08_SUCCESS_CONSTRUCTION_TOKEN_V1,
        )
    except (AttributeError, J08Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(J08RollbackCodeV1.TARGET_MISMATCH, "rollback", "target")


__all__ = (
    "FCIS_M6_J08_CERTIFICATE_SCHEMA_V1",
    "FCIS_M6_J08_SCHEMA_V1",
    "FCIS_M6_J08_STATE_SCHEMA_V1",
    "J08CompleteStateV1",
    "J08Error",
    "J08RollbackCertificateV1",
    "J08RollbackCodeV1",
    "J08RollbackReasonV1",
    "J08RollbackRejectV1",
    "J08RollbackResultV1",
    "J08RollbackSuccessV1",
    "is_verified_complete_state_v1",
    "is_verified_rollback_certificate_v1",
    "rollback_j08_v1",
)
