"""Named queued-migration disaster states, independent IR parity and admission maximality."""

from dataclasses import replace
from itertools import product
from typing import cast

from src.kernels.python.external_signal_profile_decode_v2 import transform as decode
from src.kernels.python.external_signal_profile_encode_v2 import transform as encode
from src.zenolacuna.queue_model import (
    Admission,
    QueueAction,
    QueueState,
    audit_queue,
    esso_model,
    guard_table,
    preserves_decoding,
    propose_step,
    queue_step,
)


def test_given_queued_legacy_message_when_consumer_changes_then_counterexample() -> None:
    before = audit_queue(Admission.UNGUARDED)
    assert before.complete_graph
    assert before.invariant_violations > 0 and before.misdecode_edges > 0
    assert len(before.shortest_counterexample) == 2
    after = audit_queue(Admission.PRESERVE_DECODING)
    assert after.complete_graph
    assert after.invariant_violations == after.misdecode_edges == 0
    assert after.states == 8


def test_given_pending_message_when_upgrade_rejected_then_drain_upgrade_retry() -> None:
    mode = Admission.PRESERVE_DECODING
    queued = queue_step(QueueState(), QueueAction.ENQUEUE, mode).state
    rejected = queue_step(queued, QueueAction.CONSUMER_NEW, mode)
    assert rejected.state == queued and rejected.delivered == 0
    assert rejected.code == "MIGRATION_REQUIRES_DRAIN_OR_MATCH"
    delivered = queue_step(queued, QueueAction.DELIVER, mode)
    assert delivered.delivered == 1
    duplicate = queue_step(delivered.state, QueueAction.DELIVER, mode)
    assert duplicate.code == "NO_MESSAGE" and duplicate.delivered == 0
    changed = queue_step(delivered.state, QueueAction.CONSUMER_NEW, mode).state
    changed = queue_step(changed, QueueAction.PRODUCER_NEW, mode).state
    new_message = queue_step(changed, QueueAction.ENQUEUE, mode).state
    assert queue_step(new_message, QueueAction.DELIVER, mode).delivered == 1
    assert queue_step(new_message, QueueAction.CANCEL, mode).delivered == 0


def test_every_legal_invariant_preserving_action_is_retained() -> None:
    for state, permitted in guard_table():
        for action in QueueAction:
            raw = propose_step(state, action)
            expected = raw.code == "ACCEPT" and (raw.state.queued == 0 or raw.state.consumer == raw.state.message_version)
            assert (action in permitted) == expected


def _eval(expr: dict, state: dict) -> int | bool:
    if "const" in expr:
        return expr["const"]
    if "bool" in expr:
        return expr["bool"]
    if "var" in expr:
        return state[expr["var"]]
    args = [_eval(arg, state) for arg in expr["args"]]
    if expr["op"] == "=":
        return args[0] == args[1]
    if expr["op"] == "and":
        return all(args)
    if expr["op"] == "or":
        return any(args)
    raise ValueError("unsupported_test_operator")


def test_generated_esso_guards_updates_and_effects_match_all_safe_python_states() -> None:
    model = esso_model(Admission.PRESERVE_DECODING)
    for p, c, q, v in product(range(2), repeat=4):
        if q == 0 and v != 0:
            continue
        state = QueueState(p, c, q, v)
        if not preserves_decoding(state):
            continue
        values = dict(producer=p, consumer=c, queued=q, message_version=v)
        for action in cast(list[dict], model["actions"]):
            actual = queue_step(state, QueueAction(action["id"]), Admission.PRESERVE_DECODING)
            enabled = _eval(action["guard"], values)
            assert enabled == (actual.code == "ACCEPT")
            if enabled:
                updates = {u["var"]: _eval(u["expr"], values) for u in action["updates"]}
                expected = replace(state, **updates)
                assert actual.state == expected
                assert actual.delivered == _eval(action["effects"]["delivered"], values)


def test_partial_graph_search_cannot_report_complete() -> None:
    report = audit_queue(Admission.PRESERVE_DECODING, max_states=1)
    assert not report.complete_graph


def test_concrete_codec_abstraction_preserves_each_decoding_verdict() -> None:
    # This separate direct execution oracle establishes the finite alpha-map premise.
    for producer, consumer, word in product(range(2), range(2), range(128)):
        wire = encode(word) ^ producer
        decoded = decode(wire ^ consumer)
        assert (decoded == word) == (producer == consumer)
