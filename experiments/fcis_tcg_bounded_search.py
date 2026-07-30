#!/usr/bin/env python3
"""Independent bounded search for Tree–Chord–Gate filtration mutants.

This is an explicit-state oracle, not an ESSO receipt.  It preserves the exact
finite model used to design the companion ESSO-IR file and emits deterministic
JSON suitable for cross-checking with the Julia oracle.
"""

from __future__ import annotations

import json
from collections import deque
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Final, Literal

GATE_COUNT: Final = 9
MAX_DEPTH: Final = 10
Mutation = Literal[
    "none",
    "stage_skip",
    "fake_gate",
    "lineage_without_gate",
    "lineage_conflict",
    "artifact_chord_mismatch",
]
MUTATIONS: tuple[Mutation, ...] = (
    "none",
    "stage_skip",
    "fake_gate",
    "lineage_without_gate",
    "lineage_conflict",
    "artifact_chord_mismatch",
)


@dataclass(frozen=True, slots=True, order=True)
class State:
    stage: int
    receipt_mask: int
    lineage_mask: int
    lineage_conflict: bool
    artifact_coherent: bool


@dataclass(frozen=True, slots=True)
class SearchResult:
    mutation: Mutation
    status: str
    trace: tuple[str, ...]
    trace_length: int
    reachable_states: int
    explored_transitions: int


def is_safe(state: State) -> bool:
    if not 0 <= state.stage <= GATE_COUNT:
        return False
    if state.lineage_conflict or not state.artifact_coherent:
        return False
    crossed = (1 << state.stage) - 1
    if state.receipt_mask & crossed != crossed:
        return False
    if state.lineage_mask & crossed != crossed:
        return False
    if state.lineage_mask & ~state.receipt_mask:
        return False
    return True


def successors(state: State, mutation: Mutation) -> tuple[tuple[str, State], ...]:
    outputs: list[tuple[str, State]] = [("same_stage", state)]
    if state.stage < GATE_COUNT:
        bit = 1 << state.stage
        outputs.append(
            (
                f"gate_{state.stage}",
                State(
                    state.stage + 1,
                    state.receipt_mask | bit,
                    state.lineage_mask | bit,
                    state.lineage_conflict,
                    state.artifact_coherent,
                ),
            )
        )
        if mutation == "fake_gate":
            outputs.append(
                (
                    f"fake_gate_{state.stage}",
                    State(
                        state.stage + 1,
                        state.receipt_mask,
                        state.lineage_mask | bit,
                        False,
                        True,
                    ),
                )
            )
        elif mutation == "lineage_without_gate":
            outputs.append(
                (
                    f"inject_lineage_{state.stage}",
                    State(
                        state.stage,
                        state.receipt_mask,
                        state.lineage_mask | bit,
                        False,
                        True,
                    ),
                )
            )
    if mutation == "stage_skip" and state.stage + 1 < GATE_COUNT:
        outputs.append(
            (
                "skip_to_sink",
                State(
                    GATE_COUNT,
                    state.receipt_mask,
                    state.lineage_mask,
                    False,
                    True,
                ),
            )
        )
    elif mutation == "lineage_conflict":
        outputs.append(
            (
                "overwrite_existing_role",
                State(
                    state.stage,
                    state.receipt_mask,
                    state.lineage_mask,
                    True,
                    True,
                ),
            )
        )
    elif mutation == "artifact_chord_mismatch":
        outputs.append(
            (
                "accept_mismatched_chord",
                State(
                    state.stage,
                    state.receipt_mask,
                    state.lineage_mask,
                    False,
                    False,
                ),
            )
        )
    return tuple(outputs)


def search(mutation: Mutation) -> SearchResult:
    initial = State(0, 0, 0, False, True)
    queue = deque(((initial, ()),))
    seen = {initial}
    explored = 0
    while queue:
        state, trace = queue.popleft()
        if not is_safe(state):
            return SearchResult(
                mutation=mutation,
                status="VIOLATION",
                trace=trace,
                trace_length=len(trace),
                reachable_states=len(seen),
                explored_transitions=explored,
            )
        if len(trace) == MAX_DEPTH:
            continue
        for action, successor in successors(state, mutation):
            explored += 1
            if successor not in seen:
                seen.add(successor)
                queue.append((successor, trace + (action,)))
    return SearchResult(
        mutation=mutation,
        status="SAFE_WITHIN_BOUND",
        trace=(),
        trace_length=0,
        reachable_states=len(seen),
        explored_transitions=explored,
    )


def main() -> None:
    results = tuple(search(mutation) for mutation in MUTATIONS)
    assert results[0].status == "SAFE_WITHIN_BOUND"
    for result in results[1:]:
        assert result.status == "VIOLATION"
        assert result.trace_length == 1
    payload = {
        "schema_version": "zenodex.fcis.tcg.bounded-search.v1",
        "gate_count": GATE_COUNT,
        "max_depth": MAX_DEPTH,
        "results": [asdict(result) for result in results],
    }
    output = Path(__file__).with_name("fcis_tcg_bounded_search_result.json")
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
