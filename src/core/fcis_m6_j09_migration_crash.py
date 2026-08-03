"""Bounded migration, crash, retry, and outbox model for FCIS M6 J09.

This module is a public research model.  It deliberately keeps the state
space finite while making the complete migration atom explicit:

* the seven migration phases are an exact prefix, never a skip;
* one configured writer is represented at every phase;
* a fresh authorization latch is required before a value-moving publication;
* a publication has one complete pending aggregate and is published atomically;
* PRE and POST crash observations discard or publish that aggregate;
* restart clears the active writer until fresh authorization;
* history, residuals, nullifiers, outbox rows, and effect identities have exact
  cardinality and lineage relationships;
* delivery and acknowledgment are ordered and identity-preserving.

The model is intentionally unmounted.  Its construction and transition
functions are evidence fixtures, not production authentication, storage, or
runtime authority.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, fields, replace
from enum import Enum
from typing import Callable, Final, TypeAlias

J09_MAX_WORD_DEPTH_V1: Final = 10
J09_MAX_HISTORY_V1: Final = 2
J09_MAX_GENERATION_V1: Final = 4
J09_MAX_LABEL_BYTES_V1: Final = 64


class J09PhaseV1(Enum):
    LEGACY = "LEGACY"
    SHADOW_REPLAY = "SHADOW_REPLAY"
    DUAL_CHECK = "DUAL_CHECK"
    QUIESCED = "QUIESCED"
    AUTHORITY_SWITCH = "AUTHORITY_SWITCH"
    POST_SWITCH_VALIDATION = "POST_SWITCH_VALIDATION"
    LEGACY_DISABLED = "LEGACY_DISABLED"


J09_PHASE_ORDER_V1: Final[tuple[J09PhaseV1, ...]] = tuple(J09PhaseV1)


class J09WriterV1(Enum):
    NONE = "NONE"
    LEGACY = "LEGACY"
    TARGET = "TARGET"


class J09EvidenceVersionV1(Enum):
    V1 = "V1"
    V2 = "V2"


class J09OutboxStatusV1(Enum):
    PENDING = "PENDING"
    DELIVERED = "DELIVERED"
    ACKED = "ACKED"


class J09RetryKnowledgeV1(Enum):
    NONE = "NONE"
    INDETERMINATE = "INDETERMINATE"
    CONFIRMED = "CONFIRMED"


class J09CrashObservationV1(Enum):
    NONE = "NONE"
    PRE = "PRE"
    POST = "POST"


class J09RejectCodeV1(Enum):
    NONE = "NONE"
    CRASHED = "CRASHED"
    PENDING_ATTEMPT = "PENDING_ATTEMPT"
    STALE_TOKEN = "STALE_TOKEN"
    NO_ATTEMPT = "NO_ATTEMPT"
    NO_PENDING = "NO_PENDING"
    NO_OUTBOX = "NO_OUTBOX"
    NOT_DELIVERED = "NOT_DELIVERED"
    TERMINAL_PHASE = "TERMINAL_PHASE"
    UNSUPPORTED_MUTATION = "UNSUPPORTED_MUTATION"
    HISTORY_CAPACITY = "HISTORY_CAPACITY"
    RESTART_REQUIRED = "RESTART_REQUIRED"


J09_ACTIONS_V1: Final[tuple[str, ...]] = (
    "advance_phase",
    "prepare_legacy",
    "prepare_target",
    "publish_pending",
    "retry_legacy",
    "retry_target",
    "crash_pre",
    "crash_post",
    "restart",
    "fresh_authorize",
    "deliver_outbox",
    "ack_outbox",
    "stale_legacy_commit",
    "stale_target_commit",
    "skip_phase",
    "dual_writer",
    "mixed_v1_v2_evidence",
    "rollback",
)


class J09ModelError(ValueError):
    """Raised when a public-model value or transition is malformed."""


def _label(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise J09ModelError(f"{name} must be a nonempty exact string")
    try:
        length = len(value.encode("utf-8"))
    except UnicodeEncodeError as exc:
        raise J09ModelError(f"{name} must be valid UTF-8") from exc
    if length > J09_MAX_LABEL_BYTES_V1:
        raise J09ModelError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise J09ModelError(f"{name} contains a control character")
    return value


def _bounded_u32(value: object, name: str, maximum: int) -> int:
    if type(value) is not int or value < 0 or value > maximum:
        raise J09ModelError(f"{name} is outside its closed integer bound")
    return value


def _optional_label(value: object, name: str) -> str | None:
    if value is None:
        return None
    return _label(value, name)


def _phase_index(phase: J09PhaseV1) -> int:
    return J09_PHASE_ORDER_V1.index(phase)


def _allowed_writers(phase: J09PhaseV1) -> tuple[J09WriterV1, ...]:
    if phase in (
        J09PhaseV1.LEGACY,
        J09PhaseV1.SHADOW_REPLAY,
        J09PhaseV1.DUAL_CHECK,
    ):
        return (J09WriterV1.LEGACY,)
    if phase in (J09PhaseV1.AUTHORITY_SWITCH, J09PhaseV1.LEGACY_DISABLED):
        return (J09WriterV1.TARGET,)
    return ()


def _expected_evidence(phase: J09PhaseV1) -> J09EvidenceVersionV1:
    if _phase_index(phase) < 4:
        return J09EvidenceVersionV1.V1
    return J09EvidenceVersionV1.V2


def _expected_epoch(phase: J09PhaseV1) -> int:
    return 0 if _phase_index(phase) < 4 else 1


def _attempt_fingerprint(
    commit_id: str,
    writer: J09WriterV1,
    sequence: int,
    authority_epoch: int,
    expected_head: int,
) -> str:
    return f"{commit_id}|{writer.value}|{sequence}|{authority_epoch}|{expected_head}"


@dataclass(frozen=True, slots=True)
class J09HistoryRowV1:
    """One complete history record in the bounded publication aggregate."""

    commit_id: str
    sequence: int
    writer: J09WriterV1
    authority_epoch: int
    evidence_version: J09EvidenceVersionV1
    pre_head: int
    post_head: int
    state_root: str
    residual_root: str
    nullifier: str
    effect_id: str
    fingerprint: str

    def __post_init__(self) -> None:
        _label(self.commit_id, "commit_id")
        _bounded_u32(self.sequence, "sequence", J09_MAX_HISTORY_V1)
        if self.sequence == 0:
            raise J09ModelError("sequence must be positive")
        if type(self.writer) is not J09WriterV1:
            raise J09ModelError("writer has the wrong exact type")
        _bounded_u32(self.authority_epoch, "authority_epoch", 1)
        if type(self.evidence_version) is not J09EvidenceVersionV1:
            raise J09ModelError("evidence_version has the wrong exact type")
        _bounded_u32(self.pre_head, "pre_head", J09_MAX_HISTORY_V1)
        _bounded_u32(self.post_head, "post_head", J09_MAX_HISTORY_V1)
        if self.pre_head + 1 != self.post_head or self.post_head != self.sequence:
            raise J09ModelError("history sequence and head fields diverge")
        for name, value in (
            ("state_root", self.state_root),
            ("residual_root", self.residual_root),
            ("nullifier", self.nullifier),
            ("effect_id", self.effect_id),
            ("fingerprint", self.fingerprint),
        ):
            _label(value, name)


@dataclass(frozen=True, slots=True)
class J09AttemptV1:
    """Attempt identity retained across lost responses and PRE crashes."""

    commit_id: str
    fingerprint: str
    writer: J09WriterV1
    sequence: int
    expected_head: int
    authority_epoch: int

    def __post_init__(self) -> None:
        _label(self.commit_id, "attempt.commit_id")
        _label(self.fingerprint, "attempt.fingerprint")
        if type(self.writer) is not J09WriterV1 or self.writer is J09WriterV1.NONE:
            raise J09ModelError("attempt writer is invalid")
        _bounded_u32(self.sequence, "attempt.sequence", J09_MAX_HISTORY_V1)
        if self.sequence == 0:
            raise J09ModelError("attempt sequence must be positive")
        _bounded_u32(self.expected_head, "attempt.expected_head", J09_MAX_HISTORY_V1)
        _bounded_u32(self.authority_epoch, "attempt.authority_epoch", 1)
        expected = _attempt_fingerprint(
            self.commit_id,
            self.writer,
            self.sequence,
            self.authority_epoch,
            self.expected_head,
        )
        if self.fingerprint != expected:
            raise J09ModelError("attempt fingerprint does not bind its fields")


@dataclass(frozen=True, slots=True)
class J09OutboxRowV1:
    """Outbox effect with explicit delivery and acknowledgment provenance."""

    effect_id: str
    commit_id: str
    sequence: int
    evidence_version: J09EvidenceVersionV1
    payload_root: str
    destination: str
    status: J09OutboxStatusV1
    delivery_receipt_root: str | None
    acknowledgment_root: str | None

    def __post_init__(self) -> None:
        for name, value in (
            ("effect_id", self.effect_id),
            ("commit_id", self.commit_id),
            ("payload_root", self.payload_root),
            ("destination", self.destination),
        ):
            _label(value, f"outbox.{name}")
        _bounded_u32(self.sequence, "outbox.sequence", J09_MAX_HISTORY_V1)
        if self.sequence == 0:
            raise J09ModelError("outbox sequence must be positive")
        if type(self.evidence_version) is not J09EvidenceVersionV1:
            raise J09ModelError("outbox evidence version has the wrong exact type")
        if type(self.status) is not J09OutboxStatusV1:
            raise J09ModelError("outbox status has the wrong exact type")
        _optional_label(self.delivery_receipt_root, "outbox.delivery_receipt_root")
        _optional_label(self.acknowledgment_root, "outbox.acknowledgment_root")
        if self.status is J09OutboxStatusV1.PENDING:
            if self.delivery_receipt_root is not None or self.acknowledgment_root is not None:
                raise J09ModelError("pending outbox row carries delivery evidence")
        elif self.status is J09OutboxStatusV1.DELIVERED:
            if self.delivery_receipt_root is None or self.acknowledgment_root is not None:
                raise J09ModelError("delivered outbox row has invalid evidence")
        elif self.delivery_receipt_root is None or self.acknowledgment_root is None:
            raise J09ModelError("acked outbox row has incomplete evidence")


@dataclass(frozen=True, slots=True)
class J09StateV1:
    """Complete finite state used by J09 exploration."""

    phase: J09PhaseV1
    authority_epoch: int
    allowed_writers: tuple[J09WriterV1, ...]
    active_writer: J09WriterV1
    fresh_authorization: bool
    restart_generation: int
    authorized_generation: int
    phase_trace: tuple[J09PhaseV1, ...]
    evidence_version: J09EvidenceVersionV1
    history: tuple[J09HistoryRowV1, ...]
    residual_roots: tuple[str, ...]
    nullifiers: tuple[str, ...]
    outbox: tuple[J09OutboxRowV1, ...]
    delivered_effect_ids: tuple[str, ...]
    acknowledged_effect_ids: tuple[str, ...]
    pending: J09HistoryRowV1 | None
    last_attempt: J09AttemptV1 | None
    retry_knowledge: J09RetryKnowledgeV1
    crashed: bool
    crash_observation: J09CrashObservationV1

    def __post_init__(self) -> None:
        failures = _state_failures(self)
        if failures:
            raise J09ModelError("invalid state: " + ", ".join(failures))


@dataclass(frozen=True, slots=True)
class J09TransitionV1:
    """One explored action edge, including rejected-action stutters."""

    source: J09StateV1
    action: str
    target: J09StateV1
    accepted: bool
    reject_code: J09RejectCodeV1

    def __post_init__(self) -> None:
        if type(self.source) is not J09StateV1 or type(self.target) is not J09StateV1:
            raise J09ModelError("transition endpoints have the wrong exact type")
        if self.action not in J09_ACTIONS_V1:
            raise J09ModelError("transition action is outside the closed manifest")
        if type(self.accepted) is not bool or type(self.reject_code) is not J09RejectCodeV1:
            raise J09ModelError("transition acceptance fields have the wrong type")
        if self.accepted and self.reject_code is not J09RejectCodeV1.NONE:
            raise J09ModelError("accepted transition carries a rejection code")
        if not self.accepted and self.reject_code is J09RejectCodeV1.NONE:
            raise J09ModelError("rejected transition lacks a typed rejection code")
        if not self.accepted and self.target != self.source:
            raise J09ModelError("rejected transition is not a stutter")


J09Invariant: TypeAlias = tuple[str, bool]


def _initial_state() -> J09StateV1:
    return J09StateV1(
        phase=J09PhaseV1.LEGACY,
        authority_epoch=0,
        allowed_writers=(J09WriterV1.LEGACY,),
        active_writer=J09WriterV1.LEGACY,
        fresh_authorization=True,
        restart_generation=0,
        authorized_generation=0,
        phase_trace=(J09PhaseV1.LEGACY,),
        evidence_version=J09EvidenceVersionV1.V1,
        history=(),
        residual_roots=(),
        nullifiers=(),
        outbox=(),
        delivered_effect_ids=(),
        acknowledged_effect_ids=(),
        pending=None,
        last_attempt=None,
        retry_knowledge=J09RetryKnowledgeV1.NONE,
        crashed=False,
        crash_observation=J09CrashObservationV1.NONE,
    )


def initial_state() -> J09StateV1:
    """Return the unique initial state."""

    return _initial_state()


def _safe(check: Callable[[], bool]) -> bool:
    try:
        return bool(check())
    except (AttributeError, IndexError, KeyError, TypeError, ValueError):
        return False


def _check_phase_trace(state: J09StateV1) -> bool:
    index = _phase_index(state.phase)
    return state.phase_trace == J09_PHASE_ORDER_V1[: index + 1]


def _check_phase_shape(state: J09StateV1) -> bool:
    return (
        state.allowed_writers == _allowed_writers(state.phase)
        and state.evidence_version is _expected_evidence(state.phase)
        and state.authority_epoch == _expected_epoch(state.phase)
    )


def _check_single_writer(state: J09StateV1) -> bool:
    return (
        type(state.allowed_writers) is tuple
        and len(state.allowed_writers) <= 1
        and all(
            type(writer) is J09WriterV1 and writer is not J09WriterV1.NONE
            for writer in state.allowed_writers
        )
        and (
            state.active_writer is J09WriterV1.NONE or state.active_writer in state.allowed_writers
        )
    )


def _check_authorization_latch(state: J09StateV1) -> bool:
    if state.restart_generation > J09_MAX_GENERATION_V1:
        return False
    if state.authorized_generation > state.restart_generation:
        return False
    if state.fresh_authorization:
        return (
            not state.crashed
            and state.authorized_generation == state.restart_generation
            and (
                state.active_writer is J09WriterV1.NONE
                or state.active_writer in state.allowed_writers
            )
        )
    return state.active_writer is J09WriterV1.NONE


def _check_crash_observation(state: J09StateV1) -> bool:
    if state.crashed:
        return (
            state.crash_observation in (J09CrashObservationV1.PRE, J09CrashObservationV1.POST)
            and state.pending is None
            and not state.fresh_authorization
            and state.active_writer is J09WriterV1.NONE
        )
    return state.crash_observation is J09CrashObservationV1.NONE


def _check_history(state: J09StateV1) -> bool:
    if type(state.history) is not tuple or len(state.history) > J09_MAX_HISTORY_V1:
        return False
    for sequence, row in enumerate(state.history, 1):
        if type(row) is not J09HistoryRowV1:
            return False
        if (
            row.sequence != sequence
            or row.evidence_version is not state.evidence_version
            or row.pre_head != sequence - 1
            or row.post_head != sequence
            or row.state_root != f"state-{sequence}"
            or row.residual_root != f"residual-{sequence}"
            or row.nullifier != f"nonce-{sequence}"
            or row.effect_id != f"effect-{sequence}"
            or row.fingerprint
            != _attempt_fingerprint(
                row.commit_id,
                row.writer,
                row.sequence,
                row.authority_epoch,
                row.pre_head,
            )
        ):
            return False
    return len(state.residual_roots) == len(state.history) and len(state.nullifiers) == len(
        state.history
    )


def _check_complete_roots(state: J09StateV1) -> bool:
    return (
        state.residual_roots == tuple(row.residual_root for row in state.history)
        and state.nullifiers == tuple(row.nullifier for row in state.history)
        and len(set(state.residual_roots)) == len(state.residual_roots)
        and len(set(state.nullifiers)) == len(state.nullifiers)
    )


def _check_outbox(state: J09StateV1) -> bool:
    if type(state.outbox) is not tuple or len(state.outbox) != len(state.history):
        return False
    for history_row, outbox_row in zip(state.history, state.outbox, strict=True):
        if type(outbox_row) is not J09OutboxRowV1:
            return False
        if (
            outbox_row.sequence != history_row.sequence
            or outbox_row.effect_id != history_row.effect_id
            or outbox_row.commit_id != history_row.commit_id
            or outbox_row.evidence_version is not state.evidence_version
            or outbox_row.payload_root != f"payload-{history_row.sequence}"
            or outbox_row.destination != "destination-1"
        ):
            return False
    return len({row.effect_id for row in state.outbox}) == len(state.outbox)


def _check_delivery_provenance(state: J09StateV1) -> bool:
    delivered = tuple(
        row.effect_id
        for row in state.outbox
        if row.status in (J09OutboxStatusV1.DELIVERED, J09OutboxStatusV1.ACKED)
    )
    acknowledged = tuple(
        row.effect_id for row in state.outbox if row.status is J09OutboxStatusV1.ACKED
    )
    return (
        state.delivered_effect_ids == delivered
        and state.acknowledged_effect_ids == acknowledged
        and all(
            effect_id in state.delivered_effect_ids for effect_id in state.acknowledged_effect_ids
        )
    )


def _check_evidence_version(state: J09StateV1) -> bool:
    versions = [row.evidence_version for row in state.history]
    versions.extend(row.evidence_version for row in state.outbox)
    return all(version is state.evidence_version for version in versions)


def _check_attempt_lineage(state: J09StateV1) -> bool:
    attempt = state.last_attempt
    if attempt is None:
        return state.retry_knowledge is J09RetryKnowledgeV1.NONE
    matching_history = [row for row in state.history if row.commit_id == attempt.commit_id]
    if matching_history:
        row = matching_history[0]
        return (
            state.retry_knowledge
            in (J09RetryKnowledgeV1.INDETERMINATE, J09RetryKnowledgeV1.CONFIRMED)
            and row.fingerprint == attempt.fingerprint
            and row.writer is attempt.writer
            and row.sequence == attempt.sequence
            and row.pre_head == attempt.expected_head
            and row.authority_epoch == attempt.authority_epoch
        )
    if state.pending is not None:
        return (
            state.retry_knowledge is J09RetryKnowledgeV1.NONE
            and state.pending.commit_id == attempt.commit_id
            and state.pending.fingerprint == attempt.fingerprint
            and state.pending.sequence == attempt.sequence
            and state.pending.pre_head == attempt.expected_head
        )
    return (
        state.retry_knowledge is J09RetryKnowledgeV1.NONE
        and attempt.sequence == len(state.history) + 1
        and attempt.expected_head == len(state.history)
    )


def _check_pending_lineage(state: J09StateV1) -> bool:
    pending = state.pending
    if pending is None:
        return True
    attempt = state.last_attempt
    return (
        not state.crashed
        and state.fresh_authorization
        and state.active_writer is pending.writer
        and pending.sequence == len(state.history) + 1
        and pending.pre_head == len(state.history)
        and pending.evidence_version is state.evidence_version
        and attempt is not None
        and attempt.commit_id == pending.commit_id
        and attempt.fingerprint == pending.fingerprint
    )


def _check_typed_collections(state: J09StateV1) -> bool:
    if type(state.allowed_writers) is not tuple or type(state.phase_trace) is not tuple:
        return False
    if type(state.history) is not tuple or type(state.residual_roots) is not tuple:
        return False
    if type(state.nullifiers) is not tuple or type(state.outbox) is not tuple:
        return False
    if (
        type(state.delivered_effect_ids) is not tuple
        or type(state.acknowledged_effect_ids) is not tuple
    ):
        return False
    if not all(type(phase) is J09PhaseV1 for phase in state.phase_trace):
        return False
    if not all(type(value) is str for value in state.residual_roots + state.nullifiers):
        return False
    return True


def invariant_results(state: J09StateV1) -> tuple[J09Invariant, ...]:
    """Return named invariant results; malformed witnesses fail closed."""

    checks: tuple[tuple[str, Callable[[], bool]], ...] = (
        ("typed_collections", lambda: _check_typed_collections(state)),
        ("phase_trace_exact", lambda: _check_phase_trace(state)),
        ("phase_shape_exact", lambda: _check_phase_shape(state)),
        ("single_writer", lambda: _check_single_writer(state)),
        ("authorization_latch", lambda: _check_authorization_latch(state)),
        ("crash_observation_closed", lambda: _check_crash_observation(state)),
        ("complete_history", lambda: _check_history(state)),
        ("complete_root_transport", lambda: _check_complete_roots(state)),
        ("outbox_lineage", lambda: _check_outbox(state)),
        ("evidence_version_unmixed", lambda: _check_evidence_version(state)),
        ("delivery_ack_provenance", lambda: _check_delivery_provenance(state)),
        ("attempt_lineage", lambda: _check_attempt_lineage(state)),
        ("pending_lineage", lambda: _check_pending_lineage(state)),
    )
    return tuple((name, _safe(check)) for name, check in checks)


def _state_failures(state: J09StateV1) -> tuple[str, ...]:
    return tuple(name for name, passed in invariant_results(state) if not passed)


def _transition(
    source: J09StateV1,
    action: str,
    target: J09StateV1,
    accepted: bool,
    reject_code: J09RejectCodeV1 = J09RejectCodeV1.NONE,
) -> J09TransitionV1:
    return J09TransitionV1(
        source=source,
        action=action,
        target=target,
        accepted=accepted,
        reject_code=reject_code,
    )


def _reject(state: J09StateV1, action: str, code: J09RejectCodeV1) -> J09TransitionV1:
    return _transition(state, action, state, False, code)


def _new_row(state: J09StateV1, writer: J09WriterV1, sequence: int) -> J09HistoryRowV1:
    expected_head = len(state.history)
    commit_id = f"commit-{writer.value.lower()}-{sequence}"
    return J09HistoryRowV1(
        commit_id=commit_id,
        sequence=sequence,
        writer=writer,
        authority_epoch=state.authority_epoch,
        evidence_version=state.evidence_version,
        pre_head=expected_head,
        post_head=sequence,
        state_root=f"state-{sequence}",
        residual_root=f"residual-{sequence}",
        nullifier=f"nonce-{sequence}",
        effect_id=f"effect-{sequence}",
        fingerprint=_attempt_fingerprint(
            commit_id,
            writer,
            sequence,
            state.authority_epoch,
            expected_head,
        ),
    )


def _new_attempt(row: J09HistoryRowV1) -> J09AttemptV1:
    return J09AttemptV1(
        commit_id=row.commit_id,
        fingerprint=row.fingerprint,
        writer=row.writer,
        sequence=row.sequence,
        expected_head=row.pre_head,
        authority_epoch=row.authority_epoch,
    )


def _prepare(
    state: J09StateV1,
    action: str,
    writer: J09WriterV1,
    *,
    sequence: int | None = None,
) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.RESTART_REQUIRED)
    if state.pending is not None:
        return _reject(state, action, J09RejectCodeV1.PENDING_ATTEMPT)
    if len(state.history) >= J09_MAX_HISTORY_V1:
        return _reject(state, action, J09RejectCodeV1.HISTORY_CAPACITY)
    if (
        writer not in state.allowed_writers
        or state.active_writer is not writer
        or not state.fresh_authorization
    ):
        return _reject(state, action, J09RejectCodeV1.STALE_TOKEN)
    chosen_sequence = len(state.history) + 1 if sequence is None else sequence
    if chosen_sequence != len(state.history) + 1:
        return _reject(state, action, J09RejectCodeV1.STALE_TOKEN)
    row = _new_row(state, writer, chosen_sequence)
    target = replace(
        state,
        pending=row,
        last_attempt=_new_attempt(row),
        retry_knowledge=J09RetryKnowledgeV1.NONE,
    )
    return _transition(state, action, target, True)


def _publish_pending(state: J09StateV1) -> J09StateV1:
    pending = state.pending
    if pending is None:
        raise J09ModelError("cannot publish without a pending row")
    outbox = J09OutboxRowV1(
        effect_id=pending.effect_id,
        commit_id=pending.commit_id,
        sequence=pending.sequence,
        evidence_version=pending.evidence_version,
        payload_root=f"payload-{pending.sequence}",
        destination="destination-1",
        status=J09OutboxStatusV1.PENDING,
        delivery_receipt_root=None,
        acknowledgment_root=None,
    )
    return replace(
        state,
        history=state.history + (pending,),
        residual_roots=state.residual_roots + (pending.residual_root,),
        nullifiers=state.nullifiers + (pending.nullifier,),
        outbox=state.outbox + (outbox,),
        pending=None,
        active_writer=J09WriterV1.NONE,
        fresh_authorization=False,
        retry_knowledge=J09RetryKnowledgeV1.INDETERMINATE,
    )


def _publish(state: J09StateV1, action: str) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.RESTART_REQUIRED)
    if state.pending is None:
        return _reject(state, action, J09RejectCodeV1.NO_PENDING)
    if not state.fresh_authorization or state.active_writer is not state.pending.writer:
        return _reject(state, action, J09RejectCodeV1.STALE_TOKEN)
    return _transition(state, action, _publish_pending(state), True)


def _retry(state: J09StateV1, action: str, writer: J09WriterV1) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.RESTART_REQUIRED)
    attempt = state.last_attempt
    if attempt is None or attempt.writer is not writer:
        return _reject(state, action, J09RejectCodeV1.NO_ATTEMPT)
    matching = [row for row in state.history if row.commit_id == attempt.commit_id]
    if matching:
        row = matching[0]
        if row.fingerprint != attempt.fingerprint:
            return _reject(state, action, J09RejectCodeV1.STALE_TOKEN)
        target = replace(state, retry_knowledge=J09RetryKnowledgeV1.CONFIRMED)
        return _transition(state, action, target, True)
    if state.pending is not None:
        return _reject(state, action, J09RejectCodeV1.PENDING_ATTEMPT)
    if (
        attempt.authority_epoch != state.authority_epoch
        or attempt.expected_head != len(state.history)
        or state.active_writer is not writer
        or writer not in state.allowed_writers
        or not state.fresh_authorization
    ):
        return _reject(state, action, J09RejectCodeV1.STALE_TOKEN)
    return _prepare(state, action, writer, sequence=attempt.sequence)


def _advance_phase(state: J09StateV1, action: str) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.RESTART_REQUIRED)
    if state.pending is not None:
        return _reject(state, action, J09RejectCodeV1.PENDING_ATTEMPT)
    index = _phase_index(state.phase)
    if index >= len(J09_PHASE_ORDER_V1) - 1:
        return _reject(state, action, J09RejectCodeV1.TERMINAL_PHASE)
    next_phase = J09_PHASE_ORDER_V1[index + 1]
    next_version = _expected_evidence(next_phase)
    history = tuple(replace(row, evidence_version=next_version) for row in state.history)
    outbox = tuple(replace(row, evidence_version=next_version) for row in state.outbox)
    target = replace(
        state,
        phase=next_phase,
        authority_epoch=_expected_epoch(next_phase),
        allowed_writers=_allowed_writers(next_phase),
        active_writer=J09WriterV1.NONE,
        fresh_authorization=False,
        phase_trace=state.phase_trace + (next_phase,),
        evidence_version=next_version,
        history=history,
        outbox=outbox,
    )
    return _transition(state, action, target, True)


def _fresh_authorize(state: J09StateV1, action: str) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.RESTART_REQUIRED)
    if state.pending is not None:
        return _reject(state, action, J09RejectCodeV1.PENDING_ATTEMPT)
    active = state.allowed_writers[0] if state.allowed_writers else J09WriterV1.NONE
    target = replace(
        state,
        active_writer=active,
        fresh_authorization=True,
        authorized_generation=state.restart_generation,
    )
    return _transition(state, action, target, True)


def _crash_pre(state: J09StateV1, action: str) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.CRASHED)
    target = replace(
        state,
        pending=None,
        active_writer=J09WriterV1.NONE,
        fresh_authorization=False,
        crashed=True,
        crash_observation=J09CrashObservationV1.PRE,
    )
    return _transition(state, action, target, True)


def _crash_post(state: J09StateV1, action: str) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.CRASHED)
    published = _publish_pending(state) if state.pending is not None else state
    target = replace(
        published,
        pending=None,
        active_writer=J09WriterV1.NONE,
        fresh_authorization=False,
        crashed=True,
        crash_observation=J09CrashObservationV1.POST,
    )
    return _transition(state, action, target, True)


def _restart(state: J09StateV1, action: str) -> J09TransitionV1:
    if not state.crashed:
        return _reject(state, action, J09RejectCodeV1.CRASHED)
    if state.restart_generation >= J09_MAX_GENERATION_V1:
        return _reject(state, action, J09RejectCodeV1.HISTORY_CAPACITY)
    target = replace(
        state,
        active_writer=J09WriterV1.NONE,
        fresh_authorization=False,
        restart_generation=state.restart_generation + 1,
        crashed=False,
        crash_observation=J09CrashObservationV1.NONE,
        pending=None,
    )
    return _transition(state, action, target, True)


def _deliver(state: J09StateV1, action: str) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.RESTART_REQUIRED)
    for index, row in enumerate(state.outbox):
        if row.status is J09OutboxStatusV1.PENDING:
            updated = replace(
                row,
                status=J09OutboxStatusV1.DELIVERED,
                delivery_receipt_root=f"receipt-{row.effect_id}",
            )
            outbox = state.outbox[:index] + (updated,) + state.outbox[index + 1 :]
            target = replace(
                state,
                outbox=outbox,
                delivered_effect_ids=state.delivered_effect_ids + (row.effect_id,),
            )
            return _transition(state, action, target, True)
    return _reject(state, action, J09RejectCodeV1.NO_OUTBOX)


def _ack(state: J09StateV1, action: str) -> J09TransitionV1:
    if state.crashed:
        return _reject(state, action, J09RejectCodeV1.RESTART_REQUIRED)
    for index, row in enumerate(state.outbox):
        if row.status is J09OutboxStatusV1.DELIVERED:
            if row.effect_id not in state.delivered_effect_ids:
                return _reject(state, action, J09RejectCodeV1.NOT_DELIVERED)
            updated = replace(
                row,
                status=J09OutboxStatusV1.ACKED,
                acknowledgment_root=f"ack-{row.effect_id}",
            )
            outbox = state.outbox[:index] + (updated,) + state.outbox[index + 1 :]
            target = replace(
                state,
                outbox=outbox,
                acknowledged_effect_ids=state.acknowledged_effect_ids + (row.effect_id,),
            )
            return _transition(state, action, target, True)
    return _reject(state, action, J09RejectCodeV1.NOT_DELIVERED)


def transition(state: J09StateV1, action: str) -> J09TransitionV1:
    """Apply one closed action; invalid lifecycle actions are typed stutters."""

    if type(state) is not J09StateV1 or action not in J09_ACTIONS_V1:
        raise J09ModelError("action or state is outside the closed model")
    if action == "advance_phase":
        return _advance_phase(state, action)
    if action == "prepare_legacy":
        return _prepare(state, action, J09WriterV1.LEGACY)
    if action == "prepare_target":
        return _prepare(state, action, J09WriterV1.TARGET)
    if action == "publish_pending":
        return _publish(state, action)
    if action == "retry_legacy":
        return _retry(state, action, J09WriterV1.LEGACY)
    if action == "retry_target":
        return _retry(state, action, J09WriterV1.TARGET)
    if action == "crash_pre":
        return _crash_pre(state, action)
    if action == "crash_post":
        return _crash_post(state, action)
    if action == "restart":
        return _restart(state, action)
    if action == "fresh_authorize":
        return _fresh_authorize(state, action)
    if action == "deliver_outbox":
        return _deliver(state, action)
    if action == "ack_outbox":
        return _ack(state, action)
    if action in {"stale_legacy_commit", "stale_target_commit"}:
        return _reject(state, action, J09RejectCodeV1.STALE_TOKEN)
    return _reject(state, action, J09RejectCodeV1.UNSUPPORTED_MUTATION)


@dataclass(frozen=True, slots=True)
class J09ExplorationResultV1:
    """Frozen result of the bounded breadth-first migration exploration."""

    max_depth: int
    reachable_states: int
    transitions: int
    accepted_transitions: int
    rejected_stutters: int
    invariant_checks: int
    invariant_failures: tuple[str, ...]
    killed_mutants: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.max_depth < 0 or self.reachable_states < 1 or self.transitions < 1:
            raise J09ModelError("exploration counts are outside the closed domain")
        if self.invariant_failures:
            raise J09ModelError("exploration reached an invariant failure")
        if tuple(sorted(self.killed_mutants)) != self.killed_mutants:
            raise J09ModelError("mutant labels must be ordered")

    def to_wire(self) -> dict[str, object]:
        return {
            "max_depth": self.max_depth,
            "phase_manifest": [phase.value for phase in J09_PHASE_ORDER_V1],
            "action_manifest": list(J09_ACTIONS_V1),
            "reachable_states": self.reachable_states,
            "transitions": self.transitions,
            "accepted_transitions": self.accepted_transitions,
            "rejected_stutters": self.rejected_stutters,
            "invariant_checks": self.invariant_checks,
            "invariant_failures": list(self.invariant_failures),
            "killed_mutants": list(self.killed_mutants),
        }


def _unsafe_state(state: J09StateV1, **changes: object) -> J09StateV1:
    """Build an invalid witness without invoking the production constructor."""

    candidate = object.__new__(J09StateV1)
    for field in fields(J09StateV1):
        object.__setattr__(
            candidate, field.name, changes.get(field.name, getattr(state, field.name))
        )
    return candidate


def _committed_legacy_state() -> J09StateV1:
    prepared = transition(initial_state(), "prepare_legacy")
    published = transition(prepared.target, "publish_pending")
    if not published.accepted:
        raise J09ModelError("legacy fixture did not publish")
    return published.target


def _switched_state() -> J09StateV1:
    state = _committed_legacy_state()
    for action in ("advance_phase", "advance_phase", "advance_phase", "advance_phase"):
        edge = transition(state, action)
        if not edge.accepted:
            raise J09ModelError("switch fixture did not advance")
        state = edge.target
    return state


def kill_mutants() -> tuple[str, ...]:
    """Return permanent model mutants rejected by named invariants."""

    committed = _committed_legacy_state()
    switched = _switched_state()
    prepared = transition(initial_state(), "prepare_legacy").target
    outbox = committed.outbox[0]
    acked_row = replace(
        outbox,
        status=J09OutboxStatusV1.ACKED,
        delivery_receipt_root="receipt-effect-1",
        acknowledgment_root="ack-effect-1",
    )
    mixed_row = replace(committed.history[0], evidence_version=J09EvidenceVersionV1.V1)
    rebound_outbox = replace(outbox, effect_id="effect-rebound")
    cases: tuple[tuple[str, J09StateV1], ...] = (
        (
            "ack_before_delivery",
            _unsafe_state(
                committed,
                outbox=(acked_row,),
                delivered_effect_ids=(),
                acknowledged_effect_ids=(outbox.effect_id,),
            ),
        ),
        (
            "crash_partial_observation",
            _unsafe_state(
                prepared,
                crashed=True,
                crash_observation=J09CrashObservationV1.PRE,
            ),
        ),
        (
            "dual_writers",
            _unsafe_state(
                initial_state(),
                allowed_writers=(J09WriterV1.LEGACY, J09WriterV1.TARGET),
            ),
        ),
        (
            "effect_id_rebound",
            _unsafe_state(committed, outbox=(rebound_outbox,)),
        ),
        (
            "missing_residual_transport",
            _unsafe_state(committed, residual_roots=()),
        ),
        (
            "mixed_v1_v2_evidence",
            _unsafe_state(switched, history=(mixed_row,)),
        ),
        (
            "old_writer_after_switch",
            _unsafe_state(
                switched,
                active_writer=J09WriterV1.LEGACY,
                fresh_authorization=True,
            ),
        ),
        (
            "restart_without_fresh_authorization",
            _unsafe_state(
                transition(transition(initial_state(), "crash_pre").target, "restart").target,
                active_writer=J09WriterV1.LEGACY,
                fresh_authorization=True,
            ),
        ),
        (
            "rollback_balance_only",
            _unsafe_state(
                committed,
                history=(),
                residual_roots=(),
                nullifiers=(),
                outbox=(),
                delivered_effect_ids=(),
                acknowledged_effect_ids=(),
            ),
        ),
        (
            "skipped_phase",
            _unsafe_state(
                initial_state(),
                phase=J09PhaseV1.DUAL_CHECK,
                phase_trace=(J09PhaseV1.LEGACY, J09PhaseV1.DUAL_CHECK),
            ),
        ),
    )
    killed = [name for name, state in cases if _state_failures(state)]
    return tuple(sorted(killed))


def explore(max_depth: int = J09_MAX_WORD_DEPTH_V1) -> J09ExplorationResultV1:
    """Explore every action word up to the public finite depth."""

    if type(max_depth) is not int or max_depth < 0 or max_depth > J09_MAX_WORD_DEPTH_V1:
        raise J09ModelError("exploration depth is outside the public bound")
    initial = initial_state()
    queue: deque[tuple[J09StateV1, int]] = deque([(initial, 0)])
    seen: set[J09StateV1] = {initial}
    transitions = 0
    accepted = 0
    rejected = 0
    invariant_checks = 0
    failures: list[str] = []
    while queue:
        state, depth = queue.popleft()
        for action in J09_ACTIONS_V1:
            edge = transition(state, action)
            transitions += 1
            if edge.accepted:
                accepted += 1
            else:
                rejected += 1
            for name, passed in invariant_results(edge.target):
                invariant_checks += 1
                if not passed:
                    failures.append(f"{action}:{name}")
            if depth < max_depth and edge.target not in seen:
                seen.add(edge.target)
                queue.append((edge.target, depth + 1))
    return J09ExplorationResultV1(
        max_depth=max_depth,
        reachable_states=len(seen),
        transitions=transitions,
        accepted_transitions=accepted,
        rejected_stutters=rejected,
        invariant_checks=invariant_checks,
        invariant_failures=tuple(sorted(set(failures))),
        killed_mutants=kill_mutants(),
    )


__all__ = [
    "J09_ACTIONS_V1",
    "J09_MAX_HISTORY_V1",
    "J09_MAX_WORD_DEPTH_V1",
    "J09EvidenceVersionV1",
    "J09ExplorationResultV1",
    "J09ModelError",
    "J09OutboxRowV1",
    "J09OutboxStatusV1",
    "J09PhaseV1",
    "J09RejectCodeV1",
    "J09StateV1",
    "J09TransitionV1",
    "J09WriterV1",
    "J09CrashObservationV1",
    "invariant_results",
    "explore",
    "initial_state",
    "kill_mutants",
    "transition",
]
