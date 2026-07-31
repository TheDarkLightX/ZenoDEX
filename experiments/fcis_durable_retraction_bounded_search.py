"""Independent finite oracle for the FCIS Durable Retraction Algebra checkpoint."""

from __future__ import annotations

import json
from collections import deque
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Callable, Final

MAX_DEPTH: Final = 14
SWITCH_PHASE: Final = 4
TERMINAL_PHASE: Final = 6


@dataclass(frozen=True, slots=True, order=True)
class State:
    committed: bool = False
    receipt: bool = False
    nullifier: bool = False
    outbox: bool = False
    external_effect: bool = False
    ack: bool = False
    commit_count: int = 0
    phase: int = 0
    head_authorized: bool = False
    old_writer_after_switch: bool = False
    unauthorized_publication: bool = False


def violations(state: State) -> tuple[str, ...]:
    found: list[str] = []
    publication_bits = (state.committed, state.receipt, state.nullifier, state.outbox)
    if len(set(publication_bits)) != 1:
        found.append("AtomicPublication")
    if state.external_effect and not state.outbox:
        found.append("NoEffectWithoutCommittedOutbox")
    if state.ack and (not state.external_effect or not state.outbox):
        found.append("AckHasCommittedDeliveredAncestor")
    if state.commit_count > 1:
        found.append("SameNonceAtMostOnce")
    if state.old_writer_after_switch:
        found.append("OldWriterDisabledAfterSwitch")
    if state.unauthorized_publication:
        found.append("PublicationRequiresFreshHeadAuthorization")
    if not 0 <= state.phase <= TERMINAL_PHASE:
        found.append("MigrationPhaseBound")
    return tuple(found)


def safe_actions(state: State) -> tuple[tuple[str, State], ...]:
    actions: list[tuple[str, State]] = []
    if not state.head_authorized:
        # This transition stands for a verifier-produced environment grant.
        actions.append(("receive_verified_external_grant", replace(state, head_authorized=True)))
    actions.append(("restart_reopen", replace(state, head_authorized=False)))
    actions.append(
        (
            "crash_before_linearization",
            replace(state, head_authorized=False),
        )
    )
    if not state.committed and state.phase != 3 and state.head_authorized:
        post = replace(
            state,
            committed=True,
            receipt=True,
            nullifier=True,
            outbox=True,
            commit_count=1,
            head_authorized=False,
        )
        actions.append(("atomic_commit", post))
        actions.append(("crash_after_linearization", post))
    if state.committed:
        actions.append(("retry_same_commit", state))
    if state.outbox:
        actions.append(("deliver", replace(state, external_effect=True)))
        actions.append(("deliver_then_lose_ack", replace(state, external_effect=True)))
    if state.external_effect and state.outbox and state.head_authorized:
        # Acknowledgment consumes a verified destination receipt premise.
        actions.append(
            (
                "acknowledge_verified_destination_receipt",
                replace(state, ack=True, head_authorized=False),
            )
        )
    if state.phase < TERMINAL_PHASE and state.head_authorized:
        actions.append(
            (
                "advance_migration_phase",
                replace(state, phase=state.phase + 1, head_authorized=False),
            )
        )
    return tuple(actions)


Mutator = Callable[[State], tuple[tuple[str, State], ...]]


def _mutant_split_publication(state: State) -> tuple[tuple[str, State], ...]:
    if state.committed:
        return ()
    return (("mutant_commit_state_only", replace(state, committed=True, commit_count=1)),)


def _mutant_orphan_delivery(state: State) -> tuple[tuple[str, State], ...]:
    if state.external_effect:
        return ()
    return (("mutant_deliver_without_outbox", replace(state, external_effect=True)),)


def _mutant_orphan_ack(state: State) -> tuple[tuple[str, State], ...]:
    if state.ack:
        return ()
    return (("mutant_ack_without_delivery", replace(state, ack=True)),)


def _mutant_double_commit(state: State) -> tuple[tuple[str, State], ...]:
    if not state.committed:
        return ()
    return (("mutant_second_same_nonce_commit", replace(state, commit_count=2)),)


def _mutant_old_writer(state: State) -> tuple[tuple[str, State], ...]:
    if state.phase < SWITCH_PHASE or state.old_writer_after_switch:
        return ()
    return (("mutant_old_writer_commit", replace(state, old_writer_after_switch=True)),)


def _mutant_unauthorized_publication(
    state: State,
) -> tuple[tuple[str, State], ...]:
    if state.committed or state.head_authorized or state.phase == 3:
        return ()
    return (
        (
            "mutant_publish_without_head_authorization",
            replace(
                state,
                committed=True,
                receipt=True,
                nullifier=True,
                outbox=True,
                commit_count=1,
                unauthorized_publication=True,
            ),
        ),
    )


def _mutant_selected_root_reopen(state: State) -> tuple[tuple[str, State], ...]:
    if not state.committed or not state.receipt:
        return ()
    return (("mutant_drop_receipt_keep_state_root", replace(state, receipt=False)),)


MUTANTS: Final[tuple[tuple[str, Mutator], ...]] = (
    ("split_publication", _mutant_split_publication),
    ("orphan_delivery", _mutant_orphan_delivery),
    ("orphan_ack", _mutant_orphan_ack),
    ("same_nonce_double_commit", _mutant_double_commit),
    ("old_writer_after_switch", _mutant_old_writer),
    ("unauthorized_publication", _mutant_unauthorized_publication),
    ("selected_root_reopen", _mutant_selected_root_reopen),
)


def explore_safe() -> tuple[set[State], int]:
    initial = State()
    reached = {initial}
    frontier = deque([(initial, 0)])
    transitions = 0
    while frontier:
        state, depth = frontier.popleft()
        assert not violations(state)
        if depth >= MAX_DEPTH:
            continue
        for _label, target in safe_actions(state):
            transitions += 1
            assert not violations(target)
            if target not in reached:
                reached.add(target)
                frontier.append((target, depth + 1))
    return reached, transitions


def minimize_mutant(mutator: Mutator) -> tuple[tuple[str, ...], tuple[str, ...]]:
    initial = State()
    frontier = deque([(initial, tuple())])
    seen = {initial}
    while frontier:
        state, trace = frontier.popleft()
        for label, target in mutator(state):
            broken = violations(target)
            if broken:
                return trace + (label,), broken
        if len(trace) >= MAX_DEPTH:
            continue
        for label, target in safe_actions(state):
            if target not in seen:
                seen.add(target)
                frontier.append((target, trace + (label,)))
    raise RuntimeError("mutant survived the bounded search")


def result_document() -> dict[str, object]:
    states, transitions = explore_safe()
    mutants = []
    for mutant_id, mutator in MUTANTS:
        trace, broken = minimize_mutant(mutator)
        mutants.append(
            {
                "id": mutant_id,
                "killed": True,
                "minimal_trace": list(trace),
                "violations": list(broken),
            }
        )
    return {
        "schema_version": "zenodex.fcis.durable-retraction-search.v1",
        "max_depth": MAX_DEPTH,
        "safe_reachable_state_count": len(states),
        "safe_transition_count": transitions,
        "safe_invariants": [
            "AtomicPublication",
            "NoEffectWithoutCommittedOutbox",
            "AckHasCommittedDeliveredAncestor",
            "SameNonceAtMostOnce",
            "OldWriterDisabledAfterSwitch",
            "PublicationRequiresFreshHeadAuthorization",
            "MigrationPhaseBound",
        ],
        "mutants": mutants,
    }


def main() -> None:
    document = result_document()
    rendered = json.dumps(document, indent=2, sort_keys=True) + "\n"
    output = Path(__file__).with_name("fcis_durable_retraction_bounded_search_result.json")
    output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
