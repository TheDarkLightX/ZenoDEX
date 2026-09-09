"""Independent executable oracle for the bounded real signal migration graph."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path

import pytest

from src.integration.autotrader_signal_profile import SignalProfile, encode_profile
from src.integration.autotrader_signals import (
    EXTERNAL_SIGNAL_COMPACT_SCHEMA,
    external_signal_observation_from_dict,
)
from src.zenolacuna.check import close_model
from src.zenolacuna.model import Candidate, Evidence, LacunaError, Workflow
from src.zenolacuna.ports.signal_graph_esso import (
    signal_graph_esso_model,
    verify_signal_graph_esso,
)
from src.zenolacuna.signal_migration import (
    OBSERVATIONS,
    SOURCE_PATHS,
    Action,
    CandidateMode,
    ConsumerCapability,
    Effect,
    ParseOutcome,
    ProducerVersion,
    QueuedSchema,
    State,
    TerminalOutcome,
    TransitionCode,
    candidate_matches_mode,
    check_migration,
    known_candidate_relation,
    migration_candidate,
    migration_scope,
    runtime_guarded_transition,
    safe_transition,
    source_bindings,
    unsafe_transition,
)
from tools.tau_signal_migration_case import legacy_payload

_WORDS = tuple(range(128))
_SOURCE_INDEX = {
    "route_quote_receipt": 0,
    "local_protocol_state": 1,
    "attested_external": 2,
    "advisory_external": 3,
}
_TRUST_INDEX = {"advisory": 0, "attested": 1, "verified": 2, "protocol": 3}


def _oracle_compact_payload(word: int) -> dict[str, object]:
    """Independent fixture projection; it does not call migration code."""

    payload = legacy_payload(word)
    profile = SignalProfile(
        source_index=_SOURCE_INDEX[payload["source_kind"]],
        trust_index=_TRUST_INDEX[payload["trust_tier"]],
        freshness_ok=payload["freshness_ok"],
        auth_ok=payload["auth_ok"],
        advisory_only=payload["advisory_only"],
    )
    return {
        "schema": EXTERNAL_SIGNAL_COMPACT_SCHEMA,
        "signal_id": payload["signal_id"],
        "source_id": payload["source_id"],
        "profile_code": encode_profile(profile),
        "tags": list(payload["tags"]),
    }


def _oracle_parser(schema: QueuedSchema, word: int) -> tuple[object, ...]:
    payload = legacy_payload(word) if schema is QueuedSchema.V1 else _oracle_compact_payload(word)
    metadata = legacy_payload(word)
    try:
        parsed = external_signal_observation_from_dict(payload)
    except (TypeError, ValueError, ArithmeticError) as error:
        return (
            schema.value,
            metadata["auth_ok"],
            metadata["freshness_ok"],
            ParseOutcome.PARSER_REJECT.value,
            None,
            type(error).__name__,
            str(error),
        )
    normalized = json.dumps(parsed.to_dict(), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return (
        schema.value,
        metadata["auth_ok"],
        metadata["freshness_ok"],
        ParseOutcome.PARSER_ACCEPT.value,
        normalized,
        None,
        None,
    )


def _supports(consumer: ConsumerCapability, schema: QueuedSchema) -> bool:
    if schema is QueuedSchema.EMPTY or consumer is ConsumerCapability.DUAL:
        return True
    if consumer is ConsumerCapability.OLD:
        return schema is QueuedSchema.V1
    return schema is QueuedSchema.V2


def _producer_schema(producer: ProducerVersion) -> QueuedSchema:
    return QueuedSchema.V1 if producer is ProducerVersion.V1 else QueuedSchema.V2


def _oracle_invariant(state: State) -> bool:
    return _supports(state.consumer, _producer_schema(state.producer)) and _supports(
        state.consumer,
        state.queued_schema,
    )


def _empty_observation() -> tuple[object, ...]:
    return (QueuedSchema.EMPTY.value, None, None, ParseOutcome.NOT_ATTEMPTED.value, None, None, None)


def _queue_observation(state: State) -> tuple[object, ...]:
    assert state.queued_word is not None
    metadata = legacy_payload(state.queued_word)
    return (
        state.queued_schema.value,
        metadata["auth_ok"],
        metadata["freshness_ok"],
        ParseOutcome.NOT_ATTEMPTED.value,
        None,
        None,
        None,
    )


def _host_or_parser(state: State) -> tuple[object, ...]:
    assert state.queued_word is not None
    if _supports(state.consumer, state.queued_schema):
        return _oracle_parser(state.queued_schema, state.queued_word)
    metadata = legacy_payload(state.queued_word)
    return (
        state.queued_schema.value,
        metadata["auth_ok"],
        metadata["freshness_ok"],
        ParseOutcome.HOST_CAPABILITY_REJECT.value,
        None,
        "HostCapabilityReject",
        "consumer_capability_schema_unsupported",
    )


def _projection(result: object) -> tuple[object, ...]:
    transition = result
    return (
        transition.post_state,
        transition.accepted,
        transition.code.value,
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


def _oracle_result(
    pre: State,
    post: State,
    accepted: bool,
    code: TransitionCode,
    observation: tuple[object, ...],
    terminal: TerminalOutcome = TerminalOutcome.NONE,
    effect: Effect = Effect.NONE,
) -> tuple[object, ...]:
    return (post, accepted, code.value, *observation, terminal.value, effect.value)


def _oracle_reject(
    state: State,
    code: TransitionCode,
    observation: tuple[object, ...] | None = None,
    terminal: TerminalOutcome = TerminalOutcome.NONE,
) -> tuple[object, ...]:
    return _oracle_result(state, state, False, code, _empty_observation() if observation is None else observation, terminal)


def _oracle_transition(state: State, action: Action, word: int) -> tuple[object, ...]:
    """Separate state-machine oracle for every guarded controller transition."""

    if action in (Action.DELIVER, Action.RETRY):
        if state.queued_schema is QueuedSchema.EMPTY:
            return _oracle_reject(state, TransitionCode.QUEUE_EMPTY, terminal=TerminalOutcome.NO_MESSAGE)
        if not _oracle_invariant(state):
            return _oracle_reject(state, TransitionCode.GUARD_REJECTED, _queue_observation(state))
        observation = _host_or_parser(state)
        retry = action is Action.RETRY
        if observation[3] == ParseOutcome.HOST_CAPABILITY_REJECT.value:
            terminal = TerminalOutcome.RETRY_HOST_CAPABILITY_REJECTED if retry else TerminalOutcome.HOST_CAPABILITY_REJECTED
            return _oracle_reject(state, TransitionCode.HOST_CAPABILITY_REJECTED, observation, terminal)
        if observation[3] == ParseOutcome.PARSER_REJECT.value:
            terminal = TerminalOutcome.RETRY_PARSER_REJECTED if retry else TerminalOutcome.PARSER_REJECTED
            return _oracle_reject(state, TransitionCode.ACTUAL_PARSER_REJECTED, observation, terminal)
        terminal = TerminalOutcome.RETRIED_DELIVERED if retry else TerminalOutcome.DELIVERED
        return _oracle_result(
            state,
            State(state.producer, state.consumer),
            True,
            TransitionCode.APPLIED,
            observation,
            terminal,
            Effect.DELIVERED,
        )
    if action is Action.UPGRADE_CONSUMER:
        if state.consumer is ConsumerCapability.NEW:
            return _oracle_reject(state, TransitionCode.CONSUMER_ALREADY_NEW)
        consumer = ConsumerCapability.NEW if state.consumer is ConsumerCapability.DUAL else ConsumerCapability.DUAL
        proposed = State(state.producer, consumer, state.queued_schema, state.queued_word)
        observation = _empty_observation()
    elif action is Action.ROLLBACK_CONSUMER:
        if state.consumer is ConsumerCapability.OLD:
            return _oracle_reject(state, TransitionCode.CONSUMER_ALREADY_OLD)
        consumer = ConsumerCapability.OLD if state.consumer is ConsumerCapability.DUAL else ConsumerCapability.DUAL
        proposed = State(state.producer, consumer, state.queued_schema, state.queued_word)
        observation = _empty_observation()
    elif action is Action.UPGRADE_PRODUCER:
        if state.producer is ProducerVersion.V2:
            return _oracle_reject(state, TransitionCode.PRODUCER_ALREADY_V2)
        proposed = State(ProducerVersion.V2, state.consumer, state.queued_schema, state.queued_word)
        observation = _empty_observation()
    elif action is Action.ROLLBACK_PRODUCER:
        if state.producer is ProducerVersion.V1:
            return _oracle_reject(state, TransitionCode.PRODUCER_ALREADY_V1)
        proposed = State(ProducerVersion.V1, state.consumer, state.queued_schema, state.queued_word)
        observation = _empty_observation()
    elif action is Action.ENQUEUE:
        if state.queued_schema is not QueuedSchema.EMPTY:
            return _oracle_reject(state, TransitionCode.QUEUE_FULL)
        schema = _producer_schema(state.producer)
        metadata = legacy_payload(word)
        proposed = State(state.producer, state.consumer, schema, word)
        observation = (
            schema.value,
            metadata["auth_ok"],
            metadata["freshness_ok"],
            ParseOutcome.NOT_ATTEMPTED.value,
            None,
            None,
            None,
        )
    elif action is Action.CANCEL:
        if state.queued_schema is QueuedSchema.EMPTY:
            return _oracle_reject(state, TransitionCode.QUEUE_EMPTY, terminal=TerminalOutcome.NO_MESSAGE)
        proposed = State(state.producer, state.consumer)
        observation = _host_or_parser(state)
        if not _oracle_invariant(proposed):
            return _oracle_reject(state, TransitionCode.GUARD_REJECTED, observation)
        return _oracle_result(
            state,
            proposed,
            True,
            TransitionCode.APPLIED,
            observation,
            TerminalOutcome.CANCELLED,
            Effect.CANCELLED,
        )
    else:  # pragma: no cover - Action is exhaustive and this oracle guards drift.
        raise AssertionError(action)
    if not _oracle_invariant(proposed):
        return _oracle_reject(state, TransitionCode.GUARD_REJECTED, observation)
    code = TransitionCode.ENQUEUED if action is Action.ENQUEUE else TransitionCode.APPLIED
    return _oracle_result(state, proposed, True, code, observation)


def _all_states() -> tuple[State, ...]:
    states: list[State] = []
    for producer in ProducerVersion:
        for consumer in ConsumerCapability:
            states.append(State(producer, consumer))
            for schema in (QueuedSchema.V1, QueuedSchema.V2):
                states.extend(State(producer, consumer, schema, word) for word in _WORDS)
    return tuple(states)


def test_real_parser_exactly_preserves_every_v1_v2_fixture_observation() -> None:
    for word in _WORDS:
        v1 = _oracle_parser(QueuedSchema.V1, word)
        v2 = _oracle_parser(QueuedSchema.V2, word)
        assert v1[1:] == v2[1:]


def test_guarded_controller_matches_independent_full_finite_graph_oracle() -> None:
    edges = 0
    for state in _all_states():
        for action in Action:
            words = _WORDS if action is Action.ENQUEUE else (0,)
            for word in words:
                assert _projection(safe_transition(state, action, word)) == _oracle_transition(state, action, word)
                edges += 1
    assert len(_all_states()) == 1542
    assert edges == 208_170


def test_given_consumer_first_upgrade_when_v2_message_delivers_then_parser_fields_and_effect_are_exact() -> None:
    state = State()
    state = safe_transition(state, Action.UPGRADE_CONSUMER, 0).post_state
    state = safe_transition(state, Action.UPGRADE_PRODUCER, 0).post_state
    queued = safe_transition(state, Action.ENQUEUE, 78)

    assert queued.accepted and queued.post_state.queued_schema is QueuedSchema.V2
    delivered = safe_transition(queued.post_state, Action.DELIVER, 0)
    assert delivered.accepted
    assert delivered.effect is Effect.DELIVERED
    assert delivered.terminal is TerminalOutcome.DELIVERED
    assert delivered.observation.auth_ok is True
    assert delivered.observation.freshness_ok is True
    assert delivered.observation.outcome is ParseOutcome.PARSER_ACCEPT
    assert delivered.post_state.queued_schema is QueuedSchema.EMPTY


def test_given_producer_first_upgrade_when_guarded_then_noop_and_negative_control_exposes_shortest_trace() -> None:
    guarded = safe_transition(State(), Action.UPGRADE_PRODUCER, 0)
    assert not guarded.accepted
    assert guarded.code is TransitionCode.GUARD_REJECTED
    assert guarded.pre_state == guarded.post_state and guarded.effect is Effect.NONE

    unsafe = unsafe_transition(State(), Action.UPGRADE_PRODUCER, 0)
    assert unsafe.accepted
    assert unsafe.post_state == State(ProducerVersion.V2, ConsumerCapability.OLD)

    report = check_migration(
        mode=CandidateMode.UNGUARDED,
        inputs=_WORDS,
        declared_observations=OBSERVATIONS,
    )
    assert report.code == "UNGUARDED_COUNTEREXAMPLE"
    assert report.evidence is Evidence.EXHAUSTIVE_FINITE
    assert report.smallest_counterexample is not None
    assert report.smallest_counterexample.trace == (Action.UPGRADE_PRODUCER,)


def test_given_queued_v2_when_reader_downgrades_then_guard_rejects_without_effect() -> None:
    state = State()
    state = safe_transition(state, Action.UPGRADE_CONSUMER, 0).post_state
    state = safe_transition(state, Action.UPGRADE_PRODUCER, 0).post_state
    state = safe_transition(state, Action.ENQUEUE, 78).post_state

    downgraded = safe_transition(state, Action.ROLLBACK_CONSUMER, 0)
    assert not downgraded.accepted
    assert downgraded.code is TransitionCode.GUARD_REJECTED
    assert downgraded.post_state == state
    assert downgraded.effect is Effect.NONE


def test_old_capability_is_a_host_filter_and_rejected_parser_message_remains_retryable() -> None:
    old_v2 = State(ProducerVersion.V2, ConsumerCapability.OLD, QueuedSchema.V2, 78)
    filtered = unsafe_transition(old_v2, Action.DELIVER, 0)
    assert filtered.code is TransitionCode.HOST_CAPABILITY_REJECTED
    assert filtered.observation.outcome is ParseOutcome.HOST_CAPABILITY_REJECT
    assert filtered.post_state == old_v2

    legacy_invalid = safe_transition(State(), Action.ENQUEUE, 0).post_state
    rejected = safe_transition(legacy_invalid, Action.DELIVER, 0)
    retried = safe_transition(legacy_invalid, Action.RETRY, 0)
    assert rejected.code is TransitionCode.ACTUAL_PARSER_REJECTED
    assert rejected.post_state == legacy_invalid and rejected.effect is Effect.NONE
    assert retried.terminal is TerminalOutcome.RETRY_PARSER_REJECTED


def test_scope_candidate_binding_is_relation_exact_and_safe_report_serializes_without_clock_data() -> None:
    root = Path(__file__).resolve().parents[1]
    scope = migration_scope(root)
    guarded = migration_candidate(CandidateMode.GUARDED)
    named_but_wrong = Candidate("real-signal-migration-guarded", known_candidate_relation(CandidateMode.UNGUARDED), guarded.assumptions)

    assert len(scope.contexts) == 6
    assert scope.protected[0].required[0] == (0,)
    assert candidate_matches_mode(guarded, CandidateMode.GUARDED)
    assert not candidate_matches_mode(named_but_wrong, CandidateMode.GUARDED)

    report = check_migration(
        mode=CandidateMode.GUARDED,
        inputs=_WORDS,
        declared_observations=OBSERVATIONS,
        candidate=named_but_wrong,
    )
    assert report.code == "CANDIDATE_RELATION_MISMATCH"
    assert json.dumps(asdict(report), sort_keys=True)


def test_selected_guarded_relation_closes_model_before_the_source_bound_runtime_gate() -> None:
    root = Path(__file__).resolve().parents[1]
    scope = migration_scope(root)
    report = close_model(scope, (1,), migration_candidate(CandidateMode.GUARDED))

    assert report.workflow is Workflow.COMPLETE_FOR_SCOPE
    assert report.code == "FINITE_MODEL_REPLAYED"


def test_incomplete_domain_or_observation_declaration_fails_closed() -> None:
    incomplete = check_migration(
        mode=CandidateMode.GUARDED,
        inputs=_WORDS[:-1],
        declared_observations=OBSERVATIONS,
    )
    assert incomplete.code == "INPUT_DOMAIN_INCOMPLETE"
    assert incomplete.evidence is Evidence.UNKNOWN

    bool_alias_domain = (False, True, *range(2, 128))
    bool_alias = check_migration(
        mode=CandidateMode.GUARDED,
        inputs=bool_alias_domain,
        declared_observations=OBSERVATIONS,
    )
    assert bool_alias.code == "INPUT_DOMAIN_INCOMPLETE"

    omitted = check_migration(
        mode=CandidateMode.GUARDED,
        inputs=_WORDS,
        declared_observations=tuple(value for value in OBSERVATIONS if value != "auth_ok"),
    )
    assert omitted.code == "MODEL_OMISSION"
    assert omitted.missing_observations == ("auth_ok",)


def test_runtime_guard_rejects_drifted_import_snapshot(monkeypatch: pytest.MonkeyPatch) -> None:
    import src.zenolacuna.signal_migration as migration

    monkeypatch.setattr(migration, "_PINNED_SOURCE_SHA256", ())
    result = runtime_guarded_transition(State(), Action.ENQUEUE, 78)
    assert not result.accepted
    assert result.code is TransitionCode.SOURCE_SNAPSHOT_CHANGED
    assert result.pre_state == result.post_state and result.effect is Effect.NONE


def test_archived_source_binding_must_equal_the_imported_snapshot(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[1]
    for relative in SOURCE_PATHS:
        target = tmp_path / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((root / relative).read_bytes())
    assert source_bindings(tmp_path) == source_bindings(root)

    changed = tmp_path / SOURCE_PATHS[-1]
    changed.write_bytes(changed.read_bytes() + b"\\n# stale archive\\n")
    with pytest.raises(LacunaError, match="SOURCE_BINDING_MISMATCH"):
        source_bindings(tmp_path)
    report = check_migration(
        mode=CandidateMode.GUARDED,
        inputs=_WORDS,
        declared_observations=OBSERVATIONS,
        source_root=tmp_path,
    )
    assert report.code == "SOURCE_BINDING_MISMATCH"


def test_esso_handoff_is_canonical_and_runtime_bound() -> None:
    model = signal_graph_esso_model(CandidateMode.GUARDED)
    check = verify_signal_graph_esso(model, CandidateMode.GUARDED)

    assert check.code == "ESSO_GRAPH_RUNTIME_PARITY"
    assert check.evidence is Evidence.EXHAUSTIVE_FINITE
    assert check.verified
    assert check.model_matches
    assert check.checked_guard_rows == 208_170
    assert check.checked_states == 1542
    assert check.runtime_code == "SIGNAL_MIGRATION_CHECKED"

    # A supplied action effect is interpreted; this does not rely on a second
    # invocation of the graph generator for mismatch detection.
    mutated = json.loads(json.dumps(model))
    mutated["actions"][0]["effects"]["accepted"] = {"bool": True}
    rejected = verify_signal_graph_esso(mutated, CandidateMode.GUARDED)
    assert rejected.code == "ESSO_GRAPH_RUNTIME_MISMATCH"
    assert rejected.evidence is Evidence.UNKNOWN
    assert not rejected.verified
