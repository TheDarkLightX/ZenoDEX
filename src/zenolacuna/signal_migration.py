"""Bounded V1/V2 AutoTrader signal migration controller.

The controller owns only a local, finite adapter workflow.  It has no
settlement authority.  The fixed message domain is the 128 semantic metadata
words emitted by :mod:`tools.tau_signal_migration_case`; signal parsing remains
with the mounted ``ExternalSignalObservation`` constructor.

``ConsumerCapability.OLD`` is deliberately a host-side capability filter.  It
does not describe an old binary or change the actual parser, which currently
understands both V1 and V2 payloads.  This distinction keeps a queued V2
message observable during a rolling upgrade instead of hiding it behind a
pretend legacy parser.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Final

from src.integration.autotrader_signal_profile import SignalProfile, encode_profile
from src.integration.autotrader_signals import (
    EXTERNAL_SIGNAL_COMPACT_SCHEMA,
    EXTERNAL_SIGNAL_SCHEMA,
    external_signal_observation_from_dict,
)
from tools.tau_signal_migration_case import legacy_payload

from .model import (
    Candidate,
    Evidence,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Question,
    Requirement,
    Scope,
    SourceRef,
)
from .ports.signals import replay_signal_projection

SOURCE_PATHS: Final[tuple[str, ...]] = (
    "src/zenolacuna/signal_migration.py",
    "src/zenolacuna/model.py",
    "src/zenolacuna/ports/signals.py",
    "tools/tau_signal_migration_case.py",
    "src/integration/autotrader_signals.py",
    "src/integration/autotrader_signal_profile.py",
    "src/kernels/python/external_signal_profile_encode_v2.py",
    "src/kernels/python/external_signal_profile_decode_v2.py",
    "src/kernels/python/strategy_external_signal_contract_v1_adapter.py",
)

# The exact externally observable fields for this controller.  A declaration
# must retain this order so a future observer cannot silently drop auth or
# freshness from the refinement relation.
OBSERVATIONS: Final[tuple[str, ...]] = (
    "schema",
    "auth_ok",
    "freshness_ok",
    "outcome",
    "normalized_json",
    "error_type",
    "error",
    "terminal",
    "effect",
)

_FIXTURE_FIELDS: Final[tuple[str, ...]] = (
    "advisory_only",
    "auth_ok",
    "freshness_ok",
    "schema",
    "signal_id",
    "source_id",
    "source_kind",
    "tags",
    "trust_tier",
)
_METADATA_WORDS: Final[tuple[int, ...]] = tuple(range(128))
_SOURCE_INDEX: Final[dict[str, int]] = {
    "route_quote_receipt": 0,
    "local_protocol_state": 1,
    "attested_external": 2,
    "advisory_external": 3,
}
_TRUST_INDEX: Final[dict[str, int]] = {
    "advisory": 0,
    "attested": 1,
    "verified": 2,
    "protocol": 3,
}


class ProducerVersion(str, Enum):
    """The transport schema selected by the producer for a new message."""

    V1 = "V1"
    V2 = "V2"


class ConsumerCapability(str, Enum):
    """Host capability policy applied before the real parser."""

    OLD = "OLD"
    DUAL = "DUAL"
    NEW = "NEW"


class QueuedSchema(str, Enum):
    """Exact wire schema tag retained with the one queued message."""

    EMPTY = "EMPTY"
    V1 = EXTERNAL_SIGNAL_SCHEMA
    V2 = EXTERNAL_SIGNAL_COMPACT_SCHEMA


class CandidateMode(str, Enum):
    """Controller policy candidates compared by the bounded migration check."""

    UNGUARDED = "UNGUARDED"
    GUARDED = "GUARDED"


class Action(str, Enum):
    """One finite controller operation."""

    UPGRADE_CONSUMER = "UPGRADE_CONSUMER"
    ROLLBACK_CONSUMER = "ROLLBACK_CONSUMER"
    UPGRADE_PRODUCER = "UPGRADE_PRODUCER"
    ROLLBACK_PRODUCER = "ROLLBACK_PRODUCER"
    ENQUEUE = "ENQUEUE"
    DELIVER = "DELIVER"
    RETRY = "RETRY"
    CANCEL = "CANCEL"


class TransitionCode(str, Enum):
    """Stable decision codes.  Rejections retain their exact pre-state."""

    APPLIED = "APPLIED"
    ENQUEUED = "ENQUEUED"
    QUEUE_FULL = "QUEUE_FULL"
    QUEUE_EMPTY = "QUEUE_EMPTY"
    PRODUCER_ALREADY_V2 = "PRODUCER_ALREADY_V2"
    PRODUCER_ALREADY_V1 = "PRODUCER_ALREADY_V1"
    CONSUMER_ALREADY_NEW = "CONSUMER_ALREADY_NEW"
    CONSUMER_ALREADY_OLD = "CONSUMER_ALREADY_OLD"
    GUARD_REJECTED = "GUARD_REJECTED"
    HOST_CAPABILITY_REJECTED = "HOST_CAPABILITY_REJECTED"
    ACTUAL_PARSER_REJECTED = "ACTUAL_PARSER_REJECTED"
    SOURCE_SNAPSHOT_CHANGED = "SOURCE_SNAPSHOT_CHANGED"


class ParseOutcome(str, Enum):
    """The parser or wrapper result for one queued fixed-domain message."""

    NOT_ATTEMPTED = "NOT_ATTEMPTED"
    PARSER_ACCEPT = "PARSER_ACCEPT"
    PARSER_REJECT = "PARSER_REJECT"
    HOST_CAPABILITY_REJECT = "HOST_CAPABILITY_REJECT"


class TerminalOutcome(str, Enum):
    """Terminal observation of the current controller operation."""

    NONE = "NONE"
    DELIVERED = "DELIVERED"
    RETRIED_DELIVERED = "RETRIED_DELIVERED"
    CANCELLED = "CANCELLED"
    PARSER_REJECTED = "PARSER_REJECTED"
    RETRY_PARSER_REJECTED = "RETRY_PARSER_REJECTED"
    HOST_CAPABILITY_REJECTED = "HOST_CAPABILITY_REJECTED"
    RETRY_HOST_CAPABILITY_REJECTED = "RETRY_HOST_CAPABILITY_REJECTED"
    NO_MESSAGE = "NO_MESSAGE"


class Effect(str, Enum):
    """The whole effect plan for a local controller operation."""

    NONE = "NONE"
    DELIVERED = "DELIVERED"
    CANCELLED = "CANCELLED"


@dataclass(frozen=True, slots=True)
class State:
    """Immutable one-message migration state.

    ``queued_schema`` and ``queued_word`` form one owned aggregate.  The empty
    state cannot retain a stale metadata word.
    """

    producer: ProducerVersion = ProducerVersion.V1
    consumer: ConsumerCapability = ConsumerCapability.OLD
    queued_schema: QueuedSchema = QueuedSchema.EMPTY
    queued_word: int | None = None

    def __post_init__(self) -> None:
        if type(self.producer) is not ProducerVersion:
            raise LacunaError("INVALID_PRODUCER_VERSION")
        if type(self.consumer) is not ConsumerCapability:
            raise LacunaError("INVALID_CONSUMER_CAPABILITY")
        if type(self.queued_schema) is not QueuedSchema:
            raise LacunaError("INVALID_QUEUED_SCHEMA")
        if self.queued_schema is QueuedSchema.EMPTY:
            if self.queued_word is not None:
                raise LacunaError("NONCANONICAL_EMPTY_QUEUE")
            return
        _validate_word(self.queued_word)


@dataclass(frozen=True, slots=True)
class SignalObservation:
    """Exact parser-facing observation declared by :data:`OBSERVATIONS`."""

    schema: QueuedSchema
    auth_ok: bool | None
    freshness_ok: bool | None
    outcome: ParseOutcome
    normalized_json: str | None = None
    error_type: str | None = None
    error: str | None = None

    def __post_init__(self) -> None:
        if type(self.schema) is not QueuedSchema:
            raise LacunaError("INVALID_OBSERVATION_SCHEMA")
        if type(self.outcome) is not ParseOutcome:
            raise LacunaError("INVALID_PARSE_OUTCOME")
        if self.schema is QueuedSchema.EMPTY:
            if any(value is not None for value in (self.auth_ok, self.freshness_ok)):
                raise LacunaError("EMPTY_OBSERVATION_METADATA")
            return
        if type(self.auth_ok) is not bool or type(self.freshness_ok) is not bool:
            raise LacunaError("INVALID_OBSERVATION_METADATA")


@dataclass(frozen=True, slots=True)
class Transition:
    """A pure proposed transition or a typed reject/no-op."""

    pre_state: State
    post_state: State
    action: Action
    word: int
    accepted: bool
    code: TransitionCode
    observation: SignalObservation
    terminal: TerminalOutcome
    effect: Effect

    def __post_init__(self) -> None:
        if type(self.pre_state) is not State or type(self.post_state) is not State:
            raise LacunaError("INVALID_TRANSITION_STATE")
        if type(self.action) is not Action or type(self.code) is not TransitionCode:
            raise LacunaError("INVALID_TRANSITION_ACTION")
        _validate_word(self.word)
        if type(self.accepted) is not bool:
            raise LacunaError("INVALID_TRANSITION_DECISION")
        if type(self.terminal) is not TerminalOutcome or type(self.effect) is not Effect:
            raise LacunaError("INVALID_TRANSITION_OBSERVABLE")
        if not self.accepted and self.post_state != self.pre_state:
            raise LacunaError("REJECT_MUTATES_STATE")
        if not self.accepted and self.effect is not Effect.NONE:
            raise LacunaError("REJECT_EMITS_EFFECT")


@dataclass(frozen=True, slots=True)
class Counterexample:
    """The lexicographically first shortest unsafe accepted trace."""

    trace: tuple[Action, ...]
    pre_state: State
    action: Action
    word: int
    transition: Transition


@dataclass(frozen=True, slots=True)
class MigrationReport:
    """Deterministic bounded evidence.  ``source_sha256`` uses ``SourceRef``."""

    mode: CandidateMode
    code: str
    evidence: Evidence
    candidate_relation_matches: bool
    declared_observations: tuple[str, ...]
    missing_observations: tuple[str, ...]
    unknown_observations: tuple[str, ...]
    checked_inputs128: int
    checked_states: int
    checked_edges: int
    checked_parser_pairs: int
    accepted_transitions: int
    rejected_transitions: int
    # Ordered ``(relative_path, sha256)`` pairs make ``dataclasses.asdict``
    # directly JSON serializable and let a mount compare every loaded source.
    source_sha256: tuple[tuple[str, str], ...]
    smallest_counterexample: Counterexample | None
    parser_projection_code: str
    authority: str = "NONE"
    claim: str = "BOUNDED_REAL_SIGNAL_V1_V2_MIGRATION_GRAPH"


def _validate_word(word: object) -> int:
    if type(word) is not int or word < 0 or word >= len(_METADATA_WORDS):
        raise LacunaError("INVALID_METADATA_WORD")
    return word


def _source_refs(source_root: Path) -> tuple[SourceRef, ...]:
    root = source_root.resolve(strict=True)
    return tuple(
        SourceRef(path, hashlib.sha256((root / path).read_bytes()).hexdigest())
        for path in SOURCE_PATHS
    )


_SOURCE_ROOT: Final[Path] = Path(__file__).resolve().parents[2]
_PINNED_SOURCE_SHA256: Final[tuple[SourceRef, ...]] = _source_refs(_SOURCE_ROOT)


def source_snapshot_current() -> bool:
    """Whether every imported local implementation source still matches import."""

    try:
        return _source_refs(_SOURCE_ROOT) == _PINNED_SOURCE_SHA256
    except OSError:
        return False


def source_bindings(source_root: Path) -> tuple[SourceRef, ...]:
    """Bind a source archive only when it equals the installed implementation.

    The runtime executes the modules imported from :data:`_SOURCE_ROOT`; it
    must never report hashes from a merely similarly-shaped foreign tree.  An
    archive directory is useful for project storage only when each allowlisted
    byte is equal to the import-time snapshot that this process actually uses.
    """

    refs = _source_refs(source_root)
    if refs != _PINNED_SOURCE_SHA256:
        raise LacunaError("SOURCE_BINDING_MISMATCH")
    return refs


def _schema_for_producer(producer: ProducerVersion) -> QueuedSchema:
    return QueuedSchema.V1 if producer is ProducerVersion.V1 else QueuedSchema.V2


def _consumer_supports(consumer: ConsumerCapability, schema: QueuedSchema) -> bool:
    if schema is QueuedSchema.EMPTY:
        return True
    if consumer is ConsumerCapability.DUAL:
        return True
    if consumer is ConsumerCapability.OLD:
        return schema is QueuedSchema.V1
    return schema is QueuedSchema.V2


def controller_invariant(state: State) -> bool:
    """A safe controller can emit and read the active and queued schema."""

    active_schema = _schema_for_producer(state.producer)
    return _consumer_supports(state.consumer, active_schema) and _consumer_supports(
        state.consumer,
        state.queued_schema,
    )


def _empty_observation() -> SignalObservation:
    return SignalObservation(QueuedSchema.EMPTY, None, None, ParseOutcome.NOT_ATTEMPTED)


def _fixture_metadata(word: int) -> tuple[dict[str, object], bool, bool]:
    payload = legacy_payload(word)
    auth_ok = payload.get("auth_ok")
    freshness_ok = payload.get("freshness_ok")
    if type(auth_ok) is not bool or type(freshness_ok) is not bool:
        raise LacunaError("FIXTURE_METADATA_SHAPE")
    return payload, auth_ok, freshness_ok


def _compact_payload(word: int) -> dict[str, object]:
    payload, _, _ = _fixture_metadata(word)
    source_kind = payload.get("source_kind")
    trust_tier = payload.get("trust_tier")
    tags = payload.get("tags")
    if type(source_kind) is not str or type(trust_tier) is not str or type(tags) is not list:
        raise LacunaError("FIXTURE_COMPACT_SHAPE")
    if source_kind not in _SOURCE_INDEX or trust_tier not in _TRUST_INDEX:
        raise LacunaError("FIXTURE_COMPACT_VALUE")
    profile = SignalProfile(
        source_index=_SOURCE_INDEX[source_kind],
        trust_index=_TRUST_INDEX[trust_tier],
        freshness_ok=payload["freshness_ok"],
        auth_ok=payload["auth_ok"],
        advisory_only=payload["advisory_only"],
    )
    return {
        "schema": EXTERNAL_SIGNAL_COMPACT_SCHEMA,
        "signal_id": payload["signal_id"],
        "source_id": payload["source_id"],
        "profile_code": encode_profile(profile),
        "tags": list(tags),
    }


def payload_for(schema: QueuedSchema, word: int) -> dict[str, object]:
    """Return one fixed V1 or V2 fixture payload for direct parser invocation."""

    _validate_word(word)
    if schema is QueuedSchema.V1:
        payload, _, _ = _fixture_metadata(word)
        return payload
    if schema is QueuedSchema.V2:
        return _compact_payload(word)
    raise LacunaError("EMPTY_QUEUE_HAS_NO_PAYLOAD")


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _parser_observation(schema: QueuedSchema, word: int) -> SignalObservation:
    payload, auth_ok, freshness_ok = _fixture_metadata(word)
    if schema is QueuedSchema.V2:
        payload = _compact_payload(word)
    elif schema is not QueuedSchema.V1:
        raise LacunaError("EMPTY_QUEUE_HAS_NO_PARSER")
    try:
        parsed = external_signal_observation_from_dict(payload)
    except (TypeError, ValueError, ArithmeticError) as error:
        return SignalObservation(
            schema,
            auth_ok,
            freshness_ok,
            ParseOutcome.PARSER_REJECT,
            error_type=type(error).__name__,
            error=str(error),
        )
    normalized_json = _canonical_json(parsed.to_dict())
    return SignalObservation(
        schema,
        auth_ok,
        freshness_ok,
        ParseOutcome.PARSER_ACCEPT,
        normalized_json=normalized_json,
    )


def _host_filtered_observation(state: State) -> SignalObservation:
    if state.queued_schema is QueuedSchema.EMPTY or state.queued_word is None:
        raise LacunaError("EMPTY_QUEUE_HAS_NO_PARSER")
    _, auth_ok, freshness_ok = _fixture_metadata(state.queued_word)
    if not _consumer_supports(state.consumer, state.queued_schema):
        return SignalObservation(
            state.queued_schema,
            auth_ok,
            freshness_ok,
            ParseOutcome.HOST_CAPABILITY_REJECT,
            error_type="HostCapabilityReject",
            error="consumer_capability_schema_unsupported",
        )
    return _parser_observation(state.queued_schema, state.queued_word)


def _reject(
    state: State,
    action: Action,
    word: int,
    code: TransitionCode,
    observation: SignalObservation | None = None,
    terminal: TerminalOutcome = TerminalOutcome.NONE,
) -> Transition:
    return Transition(
        state,
        state,
        action,
        word,
        False,
        code,
        _empty_observation() if observation is None else observation,
        terminal,
        Effect.NONE,
    )


def _accepted(
    pre_state: State,
    post_state: State,
    action: Action,
    word: int,
    code: TransitionCode,
    observation: SignalObservation,
    terminal: TerminalOutcome = TerminalOutcome.NONE,
    effect: Effect = Effect.NONE,
) -> Transition:
    return Transition(
        pre_state,
        post_state,
        action,
        word,
        True,
        code,
        observation,
        terminal,
        effect,
    )


def _upgrade_consumer(state: State, action: Action, word: int) -> Transition:
    if state.consumer is ConsumerCapability.NEW:
        return _reject(state, action, word, TransitionCode.CONSUMER_ALREADY_NEW)
    consumer = ConsumerCapability.DUAL
    if state.consumer is ConsumerCapability.DUAL:
        consumer = ConsumerCapability.NEW
    return _accepted(
        state,
        State(state.producer, consumer, state.queued_schema, state.queued_word),
        action,
        word,
        TransitionCode.APPLIED,
        _empty_observation(),
    )


def _rollback_consumer(state: State, action: Action, word: int) -> Transition:
    if state.consumer is ConsumerCapability.OLD:
        return _reject(state, action, word, TransitionCode.CONSUMER_ALREADY_OLD)
    consumer = ConsumerCapability.DUAL
    if state.consumer is ConsumerCapability.DUAL:
        consumer = ConsumerCapability.OLD
    return _accepted(
        state,
        State(state.producer, consumer, state.queued_schema, state.queued_word),
        action,
        word,
        TransitionCode.APPLIED,
        _empty_observation(),
    )


def _upgrade_producer(state: State, action: Action, word: int) -> Transition:
    if state.producer is ProducerVersion.V2:
        return _reject(state, action, word, TransitionCode.PRODUCER_ALREADY_V2)
    return _accepted(
        state,
        State(ProducerVersion.V2, state.consumer, state.queued_schema, state.queued_word),
        action,
        word,
        TransitionCode.APPLIED,
        _empty_observation(),
    )


def _rollback_producer(state: State, action: Action, word: int) -> Transition:
    if state.producer is ProducerVersion.V1:
        return _reject(state, action, word, TransitionCode.PRODUCER_ALREADY_V1)
    return _accepted(
        state,
        State(ProducerVersion.V1, state.consumer, state.queued_schema, state.queued_word),
        action,
        word,
        TransitionCode.APPLIED,
        _empty_observation(),
    )


def _enqueue(state: State, action: Action, word: int) -> Transition:
    if state.queued_schema is not QueuedSchema.EMPTY:
        return _reject(state, action, word, TransitionCode.QUEUE_FULL)
    schema = _schema_for_producer(state.producer)
    _, auth_ok, freshness_ok = _fixture_metadata(word)
    observation = SignalObservation(schema, auth_ok, freshness_ok, ParseOutcome.NOT_ATTEMPTED)
    return _accepted(
        state,
        State(state.producer, state.consumer, schema, word),
        action,
        word,
        TransitionCode.ENQUEUED,
        observation,
    )


def _cancel(state: State, action: Action, word: int) -> Transition:
    if state.queued_schema is QueuedSchema.EMPTY:
        return _reject(
            state,
            action,
            word,
            TransitionCode.QUEUE_EMPTY,
            terminal=TerminalOutcome.NO_MESSAGE,
        )
    return _accepted(
        state,
        State(state.producer, state.consumer),
        action,
        word,
        TransitionCode.APPLIED,
        _host_filtered_observation(state),
        TerminalOutcome.CANCELLED,
        Effect.CANCELLED,
    )


def _attempt_delivery(state: State, action: Action, word: int) -> Transition:
    if state.queued_schema is QueuedSchema.EMPTY:
        return _reject(
            state,
            action,
            word,
            TransitionCode.QUEUE_EMPTY,
            terminal=TerminalOutcome.NO_MESSAGE,
        )
    observation = _host_filtered_observation(state)
    retry = action is Action.RETRY
    if observation.outcome is ParseOutcome.HOST_CAPABILITY_REJECT:
        terminal = (
            TerminalOutcome.RETRY_HOST_CAPABILITY_REJECTED
            if retry
            else TerminalOutcome.HOST_CAPABILITY_REJECTED
        )
        return _reject(
            state,
            action,
            word,
            TransitionCode.HOST_CAPABILITY_REJECTED,
            observation,
            terminal,
        )
    if observation.outcome is ParseOutcome.PARSER_REJECT:
        terminal = TerminalOutcome.RETRY_PARSER_REJECTED if retry else TerminalOutcome.PARSER_REJECTED
        return _reject(
            state,
            action,
            word,
            TransitionCode.ACTUAL_PARSER_REJECTED,
            observation,
            terminal,
        )
    terminal = TerminalOutcome.RETRIED_DELIVERED if retry else TerminalOutcome.DELIVERED
    return _accepted(
        state,
        State(state.producer, state.consumer),
        action,
        word,
        TransitionCode.APPLIED,
        observation,
        terminal,
        Effect.DELIVERED,
    )


def _proposed_configuration_transition(state: State, action: Action, word: int) -> Transition:
    if action is Action.UPGRADE_CONSUMER:
        return _upgrade_consumer(state, action, word)
    if action is Action.ROLLBACK_CONSUMER:
        return _rollback_consumer(state, action, word)
    if action is Action.UPGRADE_PRODUCER:
        return _upgrade_producer(state, action, word)
    if action is Action.ROLLBACK_PRODUCER:
        return _rollback_producer(state, action, word)
    if action is Action.ENQUEUE:
        return _enqueue(state, action, word)
    if action is Action.CANCEL:
        return _cancel(state, action, word)
    raise LacunaError("INVALID_CONFIGURATION_ACTION")


def _validate_transition_input(state: State, action: Action, word: int) -> None:
    if type(state) is not State:
        raise LacunaError("INVALID_MIGRATION_STATE")
    if type(action) is not Action:
        raise LacunaError("INVALID_MIGRATION_ACTION")
    _validate_word(word)


def unsafe_transition(state: State, action: Action, word: int) -> Transition:
    """Propose a controller step without the migration compatibility guard.

    This negative-control candidate still runs the host filter and actual parser
    on delivery.  It does not emulate an unavailable legacy parser.
    """

    _validate_transition_input(state, action, word)
    if action in (Action.DELIVER, Action.RETRY):
        return _attempt_delivery(state, action, word)
    return _proposed_configuration_transition(state, action, word)


def safe_transition(state: State, action: Action, word: int) -> Transition:
    """Apply the guarded controller relation with typed reject/no-op behavior.

    A queued message must remain readable by the consumer and a producer's next
    schema must also be readable.  Cancellation may repair an old unsafe queue
    if its post-state satisfies the invariant; delivery and retry require a
    safe pre-state before the real parser is invoked.
    """

    _validate_transition_input(state, action, word)
    if action in (Action.DELIVER, Action.RETRY):
        if state.queued_schema is QueuedSchema.EMPTY:
            return _attempt_delivery(state, action, word)
        if not controller_invariant(state):
            observation = _empty_observation()
            if state.queued_word is not None:
                _, auth_ok, freshness_ok = _fixture_metadata(state.queued_word)
                observation = SignalObservation(
                    state.queued_schema,
                    auth_ok,
                    freshness_ok,
                    ParseOutcome.NOT_ATTEMPTED,
                )
            return _reject(state, action, word, TransitionCode.GUARD_REJECTED, observation)
        return _attempt_delivery(state, action, word)
    proposed = _proposed_configuration_transition(state, action, word)
    if proposed.accepted and not controller_invariant(proposed.post_state):
        return _reject(state, action, word, TransitionCode.GUARD_REJECTED, proposed.observation)
    return proposed


def runtime_guarded_transition(state: State, action: Action, word: int) -> Transition:
    """Source-pinned shell guard for callers mounting the pure controller.

    It checks the fixed source snapshot before and after the pure call.  A
    changed or unavailable implementation yields a reject/no-effect result so
    imported code cannot be used after its source binding has drifted.
    """

    _validate_transition_input(state, action, word)
    if not source_snapshot_current():
        return _reject(state, action, word, TransitionCode.SOURCE_SNAPSHOT_CHANGED)
    result = safe_transition(state, action, word)
    if not source_snapshot_current():
        return _reject(state, action, word, TransitionCode.SOURCE_SNAPSHOT_CHANGED)
    return result


def observable_tuple(transition: Transition) -> tuple[object, ...]:
    """Return the exact declared observation projection in :data:`OBSERVATIONS` order."""

    return (
        transition.observation.schema.value,
        transition.observation.auth_ok,
        transition.observation.freshness_ok,
        transition.observation.outcome.value,
        transition.observation.normalized_json,
        transition.observation.error_type,
        transition.observation.error,
        transition.terminal.value,
        transition.effect.value,
    )


_CONTEXTS: Final[tuple[str, ...]] = (
    "consumer_first_upgrade_v1_old_to_dual",
    "producer_first_upgrade_v1_old_to_v2_old",
    "reader_downgrade_with_queued_v2",
    "consumer_first_rollback_v2_new_to_v1_old",
    "deliver_accepted_v1_word_78",
    "deliver_accepted_v2_word_78",
)
_OUTCOMES: Final[tuple[Outcome, ...]] = (
    Outcome("safe_operation", "safe_operation", OutcomeKind.ACCEPT),
    Outcome("unsafe_operation", "unsafe_operation", OutcomeKind.ACCEPT),
    Outcome("guard_reject_no_effect", "guard_reject_no_effect", OutcomeKind.REJECT),
)
_UNGUARDED_RELATION: Final[tuple[tuple[int, ...], ...]] = (
    (0,),
    (1,),
    (1,),
    (0,),
    (0,),
    (0,),
)
_GUARDED_RELATION: Final[tuple[tuple[int, ...], ...]] = (
    (0,),
    (2,),
    (2,),
    (0,),
    (0,),
    (0,),
)
_CANDIDATE_ASSUMPTIONS: Final[tuple[int, ...]] = tuple(range(len(_CONTEXTS)))


def known_candidate_relation(mode: CandidateMode) -> tuple[tuple[int, ...], ...]:
    """The exact relation table selected by mode, independent of its name."""

    if type(mode) is not CandidateMode:
        raise LacunaError("INVALID_CANDIDATE_MODE")
    if mode is CandidateMode.GUARDED:
        return _GUARDED_RELATION
    return _UNGUARDED_RELATION


def migration_candidate(mode: CandidateMode) -> Candidate:
    """Build the explicit relation candidate for root-level model integration."""

    return Candidate(
        "real-signal-migration-" + mode.value.lower(),
        known_candidate_relation(mode),
        _CANDIDATE_ASSUMPTIONS,
    )


def candidate_matches_mode(candidate: Candidate, mode: CandidateMode) -> bool:
    """Bind a candidate to its table and assumptions without trusting its name."""

    return (
        type(candidate) is Candidate
        and candidate.allowed == known_candidate_relation(mode)
        and candidate.assumptions == _CANDIDATE_ASSUMPTIONS
    )


def migration_scope(source_root: Path) -> Scope:
    """Return the finite controller-choice scope with source-pinned inputs."""

    sources = source_bindings(source_root)
    contract = ((0,), (1, 2), (1, 2), (0,), (0,), (0,))
    protected = (
        Requirement(
            "required-positive-safe-operations",
            (0, 3, 4, 5),
            contract,
            ((0,), (), (), (0,), (0,), (0,)),
        ),
    )
    hypotheses = (
        Hypothesis("unguarded-controller", _UNGUARDED_RELATION),
        Hypothesis("guarded-controller", _GUARDED_RELATION),
    )
    question = Question(
        "migration-controller-policy",
        "Which explicit controller relation is selected for the fixed migration graph?",
        1,
        (CandidateMode.UNGUARDED.value, CandidateMode.GUARDED.value),
    )
    return Scope(
        "autotrader-real-signal-v1-v2-migration-choice",
        _CONTEXTS,
        _OUTCOMES,
        _CANDIDATE_ASSUMPTIONS,
        contract,
        protected,
        hypotheses,
        (question,),
        sources=sources,
        omission_family=(
            "fixed_128_metadata_words_only",
            "one_queued_message_only",
            "local_host_capability_filter_only",
            "no_settlement_or_release_authority",
        ),
    )


def _canonical_states() -> tuple[State, ...]:
    states: list[State] = []
    for producer in ProducerVersion:
        for consumer in ConsumerCapability:
            states.append(State(producer, consumer))
            for schema in (QueuedSchema.V1, QueuedSchema.V2):
                states.extend(State(producer, consumer, schema, word) for word in _METADATA_WORDS)
    return tuple(states)


def _action_words(action: Action, inputs: tuple[int, ...]) -> tuple[int, ...]:
    return inputs if action is Action.ENQUEUE else (inputs[0],)


def _parser_signature(observation: SignalObservation) -> tuple[object, ...]:
    return (
        observation.auth_ok,
        observation.freshness_ok,
        observation.outcome,
        observation.normalized_json,
        observation.error_type,
        observation.error,
    )


def _parser_parity_counterexample(inputs: tuple[int, ...]) -> Counterexample | None:
    for word in inputs:
        v1 = _parser_observation(QueuedSchema.V1, word)
        v2 = _parser_observation(QueuedSchema.V2, word)
        if _parser_signature(v1) == _parser_signature(v2):
            continue
        state = State(ProducerVersion.V1, ConsumerCapability.DUAL, QueuedSchema.V1, word)
        transition = _attempt_delivery(state, Action.DELIVER, word)
        return Counterexample((), state, Action.DELIVER, word, transition)
    return None


def _shortest_unsafe_counterexample(inputs: tuple[int, ...]) -> Counterexample | None:
    """Breadth-first negative control from the production V1/OLD initial state."""

    initial = State()
    pending: list[tuple[State, tuple[Action, ...]]] = [(initial, ())]
    visited = {initial}
    while pending:
        state, trace = pending.pop(0)
        for action in Action:
            for word in _action_words(action, inputs):
                transition = unsafe_transition(state, action, word)
                next_trace = trace + (action,)
                if transition.accepted and not controller_invariant(transition.post_state):
                    return Counterexample(next_trace, state, action, word, transition)
                if transition.accepted and transition.post_state not in visited:
                    visited.add(transition.post_state)
                    pending.append((transition.post_state, next_trace))
    return None


@dataclass(frozen=True, slots=True)
class _CheckContext:
    mode: CandidateMode
    declared: tuple[str, ...]
    missing: tuple[str, ...]
    unknown: tuple[str, ...]
    candidate_matches: bool
    source_sha256: tuple[SourceRef, ...]


@dataclass(frozen=True, slots=True)
class _CheckCounts:
    inputs: int = 0
    states: int = 0
    edges: int = 0
    parser_pairs: int = 0
    accepted: int = 0
    rejected: int = 0


def _report(
    context: _CheckContext,
    code: str,
    evidence: Evidence,
    counts: _CheckCounts | None = None,
    counterexample: Counterexample | None = None,
    parser_projection_code: str = "NOT_RUN",
) -> MigrationReport:
    counts = _CheckCounts() if counts is None else counts
    return MigrationReport(
        context.mode,
        code,
        evidence,
        context.candidate_matches,
        context.declared,
        context.missing,
        context.unknown,
        counts.inputs,
        counts.states,
        counts.edges,
        counts.parser_pairs,
        counts.accepted,
        counts.rejected,
        tuple((source.path, source.sha256) for source in context.source_sha256),
        counterexample,
        parser_projection_code,
    )


def _declared_observation_gaps(declared: object) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    if type(declared) is not tuple or any(type(value) is not str for value in declared):
        return (), OBSERVATIONS, ()
    missing = tuple(value for value in OBSERVATIONS if value not in declared)
    unknown = tuple(value for value in declared if value not in OBSERVATIONS)
    if declared != OBSERVATIONS or len(set(declared)) != len(declared):
        return declared, missing or OBSERVATIONS, unknown
    return declared, (), ()


def _input_domain_complete(inputs: object) -> bool:
    return (
        type(inputs) is tuple
        and len(inputs) == len(_METADATA_WORDS)
        and all(type(value) is int for value in inputs)
        and inputs == _METADATA_WORDS
    )


def _check_context(
    mode: CandidateMode,
    declared_observations: tuple[str, ...],
    source_root: Path | None,
    candidate: Candidate | None,
) -> _CheckContext | MigrationReport:
    root = _SOURCE_ROOT if source_root is None else source_root
    try:
        hashes = source_bindings(root)
    except LacunaError as error:
        context = _CheckContext(mode, (), (), (), False, ())
        code = "SOURCE_BINDING_MISMATCH" if error.code == "SOURCE_BINDING_MISMATCH" else "SOURCE_BINDING_UNAVAILABLE"
        return _report(context, code, Evidence.UNKNOWN)
    except OSError:
        context = _CheckContext(mode, (), (), (), False, ())
        return _report(context, "SOURCE_BINDING_UNAVAILABLE", Evidence.UNKNOWN)
    declared, missing, unknown = _declared_observation_gaps(declared_observations)
    selected = migration_candidate(mode) if candidate is None else candidate
    return _CheckContext(
        mode,
        declared,
        missing,
        unknown,
        candidate_matches_mode(selected, mode),
        hashes,
    )


def _preflight_report(context: _CheckContext, inputs: tuple[int, ...]) -> MigrationReport | None:
    if context.missing or context.unknown:
        return _report(context, "MODEL_OMISSION", Evidence.UNKNOWN)
    if not _input_domain_complete(inputs):
        return _report(context, "INPUT_DOMAIN_INCOMPLETE", Evidence.UNKNOWN)
    if not context.candidate_matches:
        return _report(context, "CANDIDATE_RELATION_MISMATCH", Evidence.UNKNOWN)
    if not source_snapshot_current():
        return _report(context, "SOURCE_SNAPSHOT_CHANGED", Evidence.UNKNOWN)
    return None


def _parser_parity_report(
    context: _CheckContext,
    inputs: tuple[int, ...],
) -> tuple[str, Counterexample | None, MigrationReport | None]:
    projection = replay_signal_projection(_FIXTURE_FIELDS)
    counterexample = _parser_parity_counterexample(inputs)
    if projection.code == "SIGNAL_FIXTURE_PARITY" and counterexample is None:
        return projection.code, None, None
    counts = _CheckCounts(inputs=len(inputs), parser_pairs=len(inputs))
    report = _report(
        context,
        "ACTUAL_PARSER_PARITY_MISMATCH",
        Evidence.UNKNOWN,
        counts,
        counterexample,
        projection.code,
    )
    return projection.code, counterexample, report


def _enumerate_graph(mode: CandidateMode, inputs: tuple[int, ...]) -> tuple[_CheckCounts, bool]:
    transition = safe_transition if mode is CandidateMode.GUARDED else unsafe_transition
    states = _canonical_states()
    accepted = rejected = edges = 0
    unsafe_accept = False
    for state in states:
        for action in Action:
            for word in _action_words(action, inputs):
                result = transition(state, action, word)
                edges += 1
                accepted += int(result.accepted)
                rejected += int(not result.accepted)
                unsafe_accept |= result.accepted and not controller_invariant(result.post_state)
    return _CheckCounts(len(inputs), len(states), edges, len(inputs), accepted, rejected), unsafe_accept


def _completed_graph_report(
    context: _CheckContext,
    inputs: tuple[int, ...],
    projection_code: str,
) -> MigrationReport:
    counts, unsafe_accept = _enumerate_graph(context.mode, inputs)
    if not source_snapshot_current():
        return _report(context, "SOURCE_SNAPSHOT_CHANGED", Evidence.UNKNOWN, counts, parser_projection_code=projection_code)
    counterexample = _shortest_unsafe_counterexample(inputs) if unsafe_accept else None
    code = "SIGNAL_MIGRATION_CHECKED" if counterexample is None else "UNGUARDED_COUNTEREXAMPLE"
    return _report(context, code, Evidence.EXHAUSTIVE_FINITE, counts, counterexample, projection_code)


def check_migration(
    *,
    mode: CandidateMode,
    inputs: tuple[int, ...],
    declared_observations: tuple[str, ...],
    source_root: Path | None = None,
    candidate: Candidate | None = None,
) -> MigrationReport:
    """Exhaustively check the fixed graph, real parser parity, and candidate table.

    The graph contains all 1,542 canonical controller states.  ``ENQUEUE`` is
    evaluated for every word and every other action has one canonical word
    because it does not read its argument.  Delivery and retry read each queued
    word from state, so every V1/V2 parser result is exercised without a
    redundant 128-fold action parameter.
    """

    if type(mode) is not CandidateMode:
        raise LacunaError("INVALID_CANDIDATE_MODE")
    context = _check_context(mode, declared_observations, source_root, candidate)
    if isinstance(context, MigrationReport):
        return context
    preflight = _preflight_report(context, inputs)
    if preflight is not None:
        return preflight
    projection_code, _, parity_failure = _parser_parity_report(context, inputs)
    if parity_failure is not None:
        return parity_failure
    return _completed_graph_report(context, inputs, projection_code)


__all__ = [
    "Action",
    "CandidateMode",
    "ConsumerCapability",
    "Counterexample",
    "Effect",
    "MigrationReport",
    "OBSERVATIONS",
    "ParseOutcome",
    "ProducerVersion",
    "QueuedSchema",
    "SOURCE_PATHS",
    "SignalObservation",
    "State",
    "TerminalOutcome",
    "Transition",
    "TransitionCode",
    "candidate_matches_mode",
    "check_migration",
    "controller_invariant",
    "known_candidate_relation",
    "migration_candidate",
    "migration_scope",
    "observable_tuple",
    "payload_for",
    "runtime_guarded_transition",
    "safe_transition",
    "source_bindings",
    "source_snapshot_current",
    "unsafe_transition",
]
