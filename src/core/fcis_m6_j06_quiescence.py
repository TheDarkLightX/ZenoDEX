"""Typed FCIS M6 J06 quiescence gate and no-op writer admission model.

J06 closes the migration interval in which the final replay/current-head
comparison is performed. The model is deliberately small: it does not
implement a production barrier or datastore transaction. It binds the
reviewed K01 writer set, the J04 migration evidence, the J02 QUIESCED
authority epoch, and a model-level durable snapshot witness, then makes every
covered writer attempt an explicit, state-preserving rejection.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final

from src.core import fcis_durable_retraction as dra
from src.state.canonical import canonical_json_bytes

FCIS_M6_J06_SCHEMA_V1: Final = "zenodex/fcis/m6/j06/quiescence-gate/v1"
FCIS_M6_J06_ROOT_SCHEMA_V1: Final = "zenodex/fcis/m6/j06/quiescence-root/v1"
MAX_J06_WRITERS_V1: Final = 32
MAX_J06_SEQUENCE_V1: Final = (1 << 32) - 1

_J06_GATE_CONSTRUCTION_TOKEN_V1 = object()
_J06_RESULT_CONSTRUCTION_TOKEN_V1 = object()
_HEX_DIGITS = frozenset("0123456789abcdef")

J06_REQUIRED_WRITER_IDS_V1: Final[tuple[str, ...]] = (
    "api_http_ingress",
    "background_outbox_delivery",
    "durable_recovery_worker",
    "durable_state_adapter",
    "entitlement_migration_worker",
    "governance_administrator",
    "legacy_fcis_runtime",
    "operator_cli",
    "outbox_lease_worker",
)

J06_QUIESCENCE_MARKERS_V1: Final[tuple[str, ...]] = (
    "API_WRITER_QUIESCED",
    "CLI_WRITER_QUIESCED",
    "WORKER_WRITER_QUIESCED",
    "ADMIN_WRITER_QUIESCED",
    "DIRECT_ADAPTER_WRITER_QUIESCED",
    "HEAD_REPLAY_EQUAL",
)


class J06Error(ValueError):
    """Raised when a J06 value is outside its closed research language."""


class J06RejectCodeV1(str, Enum):
    """Closed rejection classes for a writer observed at the quiescence gate."""

    ENTRYPOINT_NOT_COVERED = "entrypoint_not_covered"
    AUTHORITY_EPOCH_MISMATCH = "authority_epoch_mismatch"
    AUTHORITY_ROOT_MISMATCH = "authority_root_mismatch"
    WRITER_PROFILE_MISMATCH = "writer_profile_mismatch"
    HEAD_MISMATCH = "head_mismatch"
    SEQUENCE_MISMATCH = "sequence_mismatch"
    QUIESCED_WRITER_REJECTED = "quiesced_writer_rejected"


def _text(value: object, name: str, *, maximum_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise J06Error(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise J06Error(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise J06Error(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise J06Error(f"{name} contains a control character")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name, maximum_bytes=64)
    if len(checked) != 64 or any(character not in _HEX_DIGITS for character in checked):
        raise J06Error(f"{name} must be a lowercase SHA-256 digest")
    return checked


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0) or value > MAX_J06_SEQUENCE_V1:
        raise J06Error(f"{name} is outside its closed u32 bound")
    return value


def _ordered_texts(
    value: object,
    name: str,
    *,
    maximum: int,
    expected: tuple[str, ...] | None = None,
) -> tuple[str, ...]:
    if type(value) is not tuple or not value:
        raise J06Error(f"{name} must be a nonempty exact tuple")
    if len(value) > maximum:
        raise J06Error(f"{name} exceeds its closed bound")
    checked = tuple(_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(checked)) != len(checked):
        raise J06Error(f"{name} contains duplicates")
    if checked != tuple(sorted(checked, key=lambda item: item.encode("utf-8"))):
        raise J06Error(f"{name} is not canonically ordered")
    if expected is not None and checked != expected:
        raise J06Error(f"{name} does not match the required closed set")
    return checked


def _markers(value: object) -> tuple[str, ...]:
    if type(value) is not tuple or value != J06_QUIESCENCE_MARKERS_V1:
        raise J06Error("evidence_markers do not match the required ordered set")
    for index, marker in enumerate(value):
        _text(marker, f"evidence_markers[{index}]")
    return value


def _root(payload: object) -> str:
    return sha256(
        FCIS_M6_J06_ROOT_SCHEMA_V1.encode("ascii") + b"\x00" + canonical_json_bytes(payload)
    ).hexdigest()


@dataclass(frozen=True, slots=True)
class J06QuiescenceGateV1:
    """Verifier-owned witness that final replay comparison is quiescent."""

    manifest_root: str
    entrypoint_inventory_root: str
    phase: dra.MigrationPhaseV1
    activation_sequence: int
    authority_epoch_index: int
    authority_state_root: str
    legacy_profile_root: str
    target_profile_root: str
    current_head_root: str
    replay_head_root: str
    current_snapshot_root: str
    replay_snapshot_root: str
    replay_evidence_root: str
    covered_writer_ids: tuple[str, ...]
    evidence_markers: tuple[str, ...]
    quiescence_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J06_GATE_CONSTRUCTION_TOKEN_V1:
            raise J06Error("quiescence gate construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        _digest(self.manifest_root, "manifest_root")
        _digest(self.entrypoint_inventory_root, "entrypoint_inventory_root")
        if type(self.phase) is not dra.MigrationPhaseV1:
            raise J06Error("phase has the wrong exact type")
        if self.phase is not dra.MigrationPhaseV1.QUIESCED:
            raise J06Error("J06 gate must be in QUIESCED")
        _u32(self.activation_sequence, "activation_sequence", positive=True)
        _u32(self.authority_epoch_index, "authority_epoch_index")
        _digest(self.authority_state_root, "authority_state_root")
        legacy = _digest(self.legacy_profile_root, "legacy_profile_root")
        target = _digest(self.target_profile_root, "target_profile_root")
        if legacy == target:
            raise J06Error("legacy and target profile roots must differ")
        current = _digest(self.current_head_root, "current_head_root")
        replay = _digest(self.replay_head_root, "replay_head_root")
        if current != replay:
            raise J06Error("final replay head differs from the current head")
        current_snapshot = _digest(self.current_snapshot_root, "current_snapshot_root")
        replay_snapshot = _digest(self.replay_snapshot_root, "replay_snapshot_root")
        if current_snapshot != replay_snapshot:
            raise J06Error("final replay snapshot differs from the current snapshot")
        _digest(self.replay_evidence_root, "replay_evidence_root")
        _ordered_texts(
            self.covered_writer_ids,
            "covered_writer_ids",
            maximum=MAX_J06_WRITERS_V1,
            expected=J06_REQUIRED_WRITER_IDS_V1,
        )
        _markers(self.evidence_markers)
        expected_root = quiescence_root_v1(self)
        if _digest(self.quiescence_root, "quiescence_root") != expected_root:
            raise J06Error("quiescence_root is not canonically bound")


def quiescence_body_v1(gate: J06QuiescenceGateV1) -> dict[str, object]:
    """Return the canonical gate body without the self-referential root."""

    if type(gate) is not J06QuiescenceGateV1:
        raise J06Error("gate has the wrong exact type")
    return {
        "manifest_root": gate.manifest_root,
        "entrypoint_inventory_root": gate.entrypoint_inventory_root,
        "phase": gate.phase.value,
        "activation_sequence": gate.activation_sequence,
        "authority_epoch_index": gate.authority_epoch_index,
        "authority_state_root": gate.authority_state_root,
        "legacy_profile_root": gate.legacy_profile_root,
        "target_profile_root": gate.target_profile_root,
        "current_head_root": gate.current_head_root,
        "replay_head_root": gate.replay_head_root,
        "current_snapshot_root": gate.current_snapshot_root,
        "replay_snapshot_root": gate.replay_snapshot_root,
        "replay_evidence_root": gate.replay_evidence_root,
        "covered_writer_ids": list(gate.covered_writer_ids),
        "evidence_markers": list(gate.evidence_markers),
    }


def quiescence_root_v1(gate: J06QuiescenceGateV1) -> str:
    """Derive the canonical root for a J06 gate."""

    return _root(quiescence_body_v1(gate))


def _strict_body(body: object) -> dict[str, object]:
    if type(body) is not dict:
        raise J06Error("quiescence body must be an exact mapping")
    expected = {
        "manifest_root",
        "entrypoint_inventory_root",
        "phase",
        "activation_sequence",
        "authority_epoch_index",
        "authority_state_root",
        "legacy_profile_root",
        "target_profile_root",
        "current_head_root",
        "replay_head_root",
        "current_snapshot_root",
        "replay_snapshot_root",
        "replay_evidence_root",
        "covered_writer_ids",
        "evidence_markers",
    }
    if set(body) != expected:
        raise J06Error("quiescence body fields are not exact")
    phase_raw = body["phase"]
    if type(phase_raw) is not str:
        raise J06Error("phase must be an exact string")
    try:
        phase = dra.MigrationPhaseV1(phase_raw)
    except ValueError as exc:
        raise J06Error("phase is outside the closed enum") from exc
    if phase is not dra.MigrationPhaseV1.QUIESCED:
        raise J06Error("J06 body must be in QUIESCED")
    current_head = _digest(body["current_head_root"], "current_head_root")
    replay_head = _digest(body["replay_head_root"], "replay_head_root")
    if current_head != replay_head:
        raise J06Error("final replay head differs from the current head")
    current_snapshot = _digest(body["current_snapshot_root"], "current_snapshot_root")
    replay_snapshot = _digest(body["replay_snapshot_root"], "replay_snapshot_root")
    if current_snapshot != replay_snapshot:
        raise J06Error("final replay snapshot differs from the current snapshot")
    raw_writers = body["covered_writer_ids"]
    raw_markers = body["evidence_markers"]
    if type(raw_writers) is not list or type(raw_markers) is not list:
        raise J06Error("quiescence body collections must be exact lists")
    writers = tuple(
        _text(item, f"covered_writer_ids[{index}]") for index, item in enumerate(raw_writers)
    )
    markers = tuple(
        _text(item, f"evidence_markers[{index}]") for index, item in enumerate(raw_markers)
    )
    _ordered_texts(
        writers,
        "covered_writer_ids",
        maximum=MAX_J06_WRITERS_V1,
        expected=J06_REQUIRED_WRITER_IDS_V1,
    )
    _markers(markers)
    return {
        "manifest_root": _digest(body["manifest_root"], "manifest_root"),
        "entrypoint_inventory_root": _digest(
            body["entrypoint_inventory_root"], "entrypoint_inventory_root"
        ),
        "phase": phase.value,
        "activation_sequence": _u32(
            body["activation_sequence"], "activation_sequence", positive=True
        ),
        "authority_epoch_index": _u32(body["authority_epoch_index"], "authority_epoch_index"),
        "authority_state_root": _digest(body["authority_state_root"], "authority_state_root"),
        "legacy_profile_root": _digest(body["legacy_profile_root"], "legacy_profile_root"),
        "target_profile_root": _digest(body["target_profile_root"], "target_profile_root"),
        "current_head_root": current_head,
        "replay_head_root": replay_head,
        "current_snapshot_root": current_snapshot,
        "replay_snapshot_root": replay_snapshot,
        "replay_evidence_root": _digest(body["replay_evidence_root"], "replay_evidence_root"),
        "covered_writer_ids": list(writers),
        "evidence_markers": list(markers),
    }


def quiescence_root_from_body_v1(body: dict[str, object]) -> str:
    """Validate and derive a root from one exact candidate body."""

    return _root(_strict_body(body))


def _mint_gate_v1(
    *,
    manifest_root: str,
    entrypoint_inventory_root: str,
    phase: dra.MigrationPhaseV1,
    activation_sequence: int,
    authority_epoch_index: int,
    authority_state_root: str,
    legacy_profile_root: str,
    target_profile_root: str,
    current_head_root: str,
    replay_head_root: str,
    current_snapshot_root: str,
    replay_snapshot_root: str,
    replay_evidence_root: str,
    covered_writer_ids: tuple[str, ...],
    evidence_markers: tuple[str, ...],
    quiescence_root: str,
) -> J06QuiescenceGateV1:
    return J06QuiescenceGateV1(
        manifest_root=manifest_root,
        entrypoint_inventory_root=entrypoint_inventory_root,
        phase=phase,
        activation_sequence=activation_sequence,
        authority_epoch_index=authority_epoch_index,
        authority_state_root=authority_state_root,
        legacy_profile_root=legacy_profile_root,
        target_profile_root=target_profile_root,
        current_head_root=current_head_root,
        replay_head_root=replay_head_root,
        current_snapshot_root=current_snapshot_root,
        replay_snapshot_root=replay_snapshot_root,
        replay_evidence_root=replay_evidence_root,
        covered_writer_ids=covered_writer_ids,
        evidence_markers=evidence_markers,
        quiescence_root=quiescence_root,
        _construction_token=_J06_GATE_CONSTRUCTION_TOKEN_V1,
    )


def quiescence_payload_v1(gate: J06QuiescenceGateV1) -> dict[str, object]:
    """Return the complete wire payload for a J06 gate."""

    if type(gate) is not J06QuiescenceGateV1:
        raise J06Error("gate has the wrong exact type")
    gate._validate_fields()
    return {
        "schema": FCIS_M6_J06_SCHEMA_V1,
        **quiescence_body_v1(gate),
        "quiescence_root": gate.quiescence_root,
    }


@dataclass(frozen=True, slots=True)
class J06WriterAttemptV1:
    """A writer request presented to the quiescence admission boundary."""

    publisher_id: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    expected_head_root: str
    commit_id: str
    command_root: str
    sequence: int

    def __post_init__(self) -> None:
        _text(self.publisher_id, "publisher_id")
        _digest(self.writer_profile_root, "writer_profile_root")
        _u32(self.authority_epoch_index, "authority_epoch_index")
        _digest(self.authority_state_root, "authority_state_root")
        _digest(self.expected_head_root, "expected_head_root")
        _digest(self.commit_id, "commit_id")
        _digest(self.command_root, "command_root")
        _u32(self.sequence, "sequence", positive=True)


def writer_attempt_body_v1(attempt: J06WriterAttemptV1) -> dict[str, object]:
    """Return the complete canonical body of one attempted writer action."""

    if type(attempt) is not J06WriterAttemptV1:
        raise J06Error("attempt has the wrong exact type")
    attempt.__post_init__()
    return {
        "publisher_id": attempt.publisher_id,
        "writer_profile_root": attempt.writer_profile_root,
        "authority_epoch_index": attempt.authority_epoch_index,
        "authority_state_root": attempt.authority_state_root,
        "expected_head_root": attempt.expected_head_root,
        "commit_id": attempt.commit_id,
        "command_root": attempt.command_root,
        "sequence": attempt.sequence,
    }


def writer_attempt_root_v1(attempt: J06WriterAttemptV1) -> str:
    """Derive the canonical identity of every field in one writer attempt."""

    return _root(writer_attempt_body_v1(attempt))


@dataclass(frozen=True, slots=True)
class J06AdmissionResultV1:
    """Verifier-owned, state-preserving outcome of a J06 writer attempt."""

    gate_root: str
    attempt_root: str
    publisher_id: str
    writer_profile_root: str
    attempt_authority_epoch_index: int
    attempt_authority_state_root: str
    attempt_expected_head_root: str
    attempt_sequence: int
    command_root: str
    commit_id: str
    code: J06RejectCodeV1
    accepted: bool
    state_unchanged: bool
    pre_head_root: str
    post_head_root: str
    pre_snapshot_root: str
    post_snapshot_root: str
    pre_authority_state_root: str
    post_authority_state_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _J06_RESULT_CONSTRUCTION_TOKEN_V1:
            raise J06Error("J06 admission-result construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
        _digest(self.gate_root, "gate_root")
        _digest(self.attempt_root, "attempt_root")
        _text(self.publisher_id, "publisher_id")
        _digest(self.writer_profile_root, "writer_profile_root")
        _u32(
            self.attempt_authority_epoch_index,
            "attempt_authority_epoch_index",
        )
        _digest(self.attempt_authority_state_root, "attempt_authority_state_root")
        _digest(self.attempt_expected_head_root, "attempt_expected_head_root")
        _u32(self.attempt_sequence, "attempt_sequence", positive=True)
        _digest(self.command_root, "command_root")
        _digest(self.commit_id, "commit_id")
        if type(self.code) is not J06RejectCodeV1:
            raise J06Error("rejection code has the wrong exact type")
        if type(self.accepted) is not bool or self.accepted:
            raise J06Error("J06 cannot produce an accepted writer result")
        if type(self.state_unchanged) is not bool or not self.state_unchanged:
            raise J06Error("J06 rejection must preserve state")
        pre_head = _digest(self.pre_head_root, "pre_head_root")
        post_head = _digest(self.post_head_root, "post_head_root")
        pre_snapshot = _digest(self.pre_snapshot_root, "pre_snapshot_root")
        post_snapshot = _digest(self.post_snapshot_root, "post_snapshot_root")
        pre_authority = _digest(self.pre_authority_state_root, "pre_authority_state_root")
        post_authority = _digest(self.post_authority_state_root, "post_authority_state_root")
        if (
            pre_head != post_head
            or pre_snapshot != post_snapshot
            or pre_authority != post_authority
        ):
            raise J06Error("a J06 rejection changed authoritative state")
        attempt = J06WriterAttemptV1(
            publisher_id=self.publisher_id,
            writer_profile_root=self.writer_profile_root,
            authority_epoch_index=self.attempt_authority_epoch_index,
            authority_state_root=self.attempt_authority_state_root,
            expected_head_root=self.attempt_expected_head_root,
            commit_id=self.commit_id,
            command_root=self.command_root,
            sequence=self.attempt_sequence,
        )
        if writer_attempt_root_v1(attempt) != self.attempt_root:
            raise J06Error("attempt_root is not canonically bound")

    def to_wire(self) -> dict[str, object]:
        self._validate_fields()
        return {
            "gate_root": self.gate_root,
            "attempt_root": self.attempt_root,
            "publisher_id": self.publisher_id,
            "writer_profile_root": self.writer_profile_root,
            "attempt_authority_epoch_index": self.attempt_authority_epoch_index,
            "attempt_authority_state_root": self.attempt_authority_state_root,
            "attempt_expected_head_root": self.attempt_expected_head_root,
            "attempt_sequence": self.attempt_sequence,
            "command_root": self.command_root,
            "commit_id": self.commit_id,
            "code": self.code.value,
            "accepted": self.accepted,
            "state_unchanged": self.state_unchanged,
            "pre_head_root": self.pre_head_root,
            "post_head_root": self.post_head_root,
            "pre_snapshot_root": self.pre_snapshot_root,
            "post_snapshot_root": self.post_snapshot_root,
            "pre_authority_state_root": self.pre_authority_state_root,
            "post_authority_state_root": self.post_authority_state_root,
        }


def _mint_result_v1(
    *,
    gate: J06QuiescenceGateV1,
    attempt: J06WriterAttemptV1,
    code: J06RejectCodeV1,
) -> J06AdmissionResultV1:
    return J06AdmissionResultV1(
        gate_root=gate.quiescence_root,
        attempt_root=writer_attempt_root_v1(attempt),
        publisher_id=attempt.publisher_id,
        writer_profile_root=attempt.writer_profile_root,
        attempt_authority_epoch_index=attempt.authority_epoch_index,
        attempt_authority_state_root=attempt.authority_state_root,
        attempt_expected_head_root=attempt.expected_head_root,
        attempt_sequence=attempt.sequence,
        command_root=attempt.command_root,
        commit_id=attempt.commit_id,
        code=code,
        accepted=False,
        state_unchanged=True,
        pre_head_root=gate.current_head_root,
        post_head_root=gate.current_head_root,
        pre_snapshot_root=gate.current_snapshot_root,
        post_snapshot_root=gate.current_snapshot_root,
        pre_authority_state_root=gate.authority_state_root,
        post_authority_state_root=gate.authority_state_root,
        _construction_token=_J06_RESULT_CONSTRUCTION_TOKEN_V1,
    )


def reject_writer_v1(
    gate: J06QuiescenceGateV1,
    attempt: J06WriterAttemptV1,
) -> J06AdmissionResultV1:
    """Reject a writer attempt while preserving the observed state exactly."""

    if type(gate) is not J06QuiescenceGateV1:
        raise J06Error("gate has the wrong exact type")
    gate._validate_fields()
    if type(attempt) is not J06WriterAttemptV1:
        raise J06Error("attempt has the wrong exact type")
    attempt.__post_init__()
    if attempt.publisher_id not in gate.covered_writer_ids:
        code = J06RejectCodeV1.ENTRYPOINT_NOT_COVERED
    elif attempt.authority_epoch_index != gate.authority_epoch_index:
        code = J06RejectCodeV1.AUTHORITY_EPOCH_MISMATCH
    elif attempt.authority_state_root != gate.authority_state_root:
        code = J06RejectCodeV1.AUTHORITY_ROOT_MISMATCH
    elif attempt.writer_profile_root not in (
        gate.legacy_profile_root,
        gate.target_profile_root,
    ):
        code = J06RejectCodeV1.WRITER_PROFILE_MISMATCH
    elif attempt.expected_head_root != gate.current_head_root:
        code = J06RejectCodeV1.HEAD_MISMATCH
    elif attempt.sequence != gate.activation_sequence:
        code = J06RejectCodeV1.SEQUENCE_MISMATCH
    else:
        code = J06RejectCodeV1.QUIESCED_WRITER_REJECTED
    return _mint_result_v1(gate=gate, attempt=attempt, code=code)


__all__ = [
    "FCIS_M6_J06_ROOT_SCHEMA_V1",
    "FCIS_M6_J06_SCHEMA_V1",
    "J06AdmissionResultV1",
    "J06Error",
    "J06QuiescenceGateV1",
    "J06RejectCodeV1",
    "J06WriterAttemptV1",
    "J06_QUIESCENCE_MARKERS_V1",
    "J06_REQUIRED_WRITER_IDS_V1",
    "quiescence_body_v1",
    "quiescence_payload_v1",
    "quiescence_root_from_body_v1",
    "quiescence_root_v1",
    "reject_writer_v1",
    "writer_attempt_body_v1",
    "writer_attempt_root_v1",
]
