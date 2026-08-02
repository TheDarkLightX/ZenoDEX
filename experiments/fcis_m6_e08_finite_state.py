"""Public bounded finite-state model for E08 commit/migration words.

The model is intentionally small and explicit. Commands A and B share one
nonce/nullifier and compete for the same predecessor head. A publication is
one atomic transition that advances the head and records its commit and
nullifier together. Quiescence and authority switch are monotone barriers.
Rejected actions are stutters and never change the state.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

E08_MAX_WORD_DEPTH_V1: Final = 6
E08_ACTIONS_V1: Final[tuple[str, ...]] = (
    "commit_a",
    "commit_b",
    "retry_a",
    "retry_b",
    "quiesce",
    "authority_switch",
)


class E08PhaseV1(Enum):
    ACTIVE = "active"
    QUIESCED = "quiesced"
    SWITCHED = "switched"


class E08ModelError(ValueError):
    """Raised when a bounded-model value or transition is malformed."""


@dataclass(frozen=True, slots=True, order=True)
class E08StateV1:
    """Complete finite state used by the public explorer."""

    head: int
    authority_epoch: int
    phase: E08PhaseV1
    committed_ids: tuple[str, ...]
    nullifiers: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.head) is not int or self.head not in (0, 1):
            raise E08ModelError("head is outside the bounded model")
        if type(self.authority_epoch) is not int or self.authority_epoch not in (0, 1):
            raise E08ModelError("authority epoch is outside the bounded model")
        if type(self.phase) is not E08PhaseV1:
            raise E08ModelError("phase has the wrong exact type")
        if type(self.committed_ids) is not tuple or type(self.nullifiers) is not tuple:
            raise E08ModelError("state collections must be exact tuples")
        if tuple(sorted(self.committed_ids)) != self.committed_ids:
            raise E08ModelError("commit IDs must be ordered")
        if tuple(sorted(self.nullifiers)) != self.nullifiers:
            raise E08ModelError("nullifiers must be ordered")
        if len(set(self.committed_ids)) != len(self.committed_ids):
            raise E08ModelError("commit IDs must be unique")
        if len(set(self.nullifiers)) != len(self.nullifiers):
            raise E08ModelError("nullifiers must be unique")
        if any(nullifier != "nonce-alice-7" for nullifier in self.nullifiers):
            raise E08ModelError("nullifier is outside the bounded sender/nonce domain")
        if len(self.committed_ids) != self.head or len(self.nullifiers) != self.head:
            raise E08ModelError("head and publication/nullifier cardinalities diverge")
        if self.phase is E08PhaseV1.ACTIVE and self.authority_epoch != 0:
            raise E08ModelError("active phase has a future authority epoch")
        if self.phase is E08PhaseV1.QUIESCED and self.authority_epoch != 0:
            raise E08ModelError("quiesced phase has a future authority epoch")
        if self.phase is E08PhaseV1.SWITCHED and self.authority_epoch != 1:
            raise E08ModelError("switched phase lacks the authority epoch advance")


@dataclass(frozen=True, slots=True)
class E08TransitionV1:
    """One explored action edge, including rejected-action stutters."""

    source: E08StateV1
    action: str
    target: E08StateV1
    accepted: bool

    def __post_init__(self) -> None:
        if self.action not in E08_ACTIONS_V1:
            raise E08ModelError("transition action is outside the manifest")
        if type(self.accepted) is not bool:
            raise E08ModelError("accepted must be an exact Boolean")


E08Invariant: TypeAlias = tuple[str, bool]


def initial_state() -> E08StateV1:
    return E08StateV1(
        head=0,
        authority_epoch=0,
        phase=E08PhaseV1.ACTIVE,
        committed_ids=(),
        nullifiers=(),
    )


def _commit(state: E08StateV1, commit_id: str) -> tuple[E08StateV1, bool]:
    if commit_id in state.committed_ids:
        return state, False
    if state.phase is not E08PhaseV1.ACTIVE or state.authority_epoch != 0:
        return state, False
    if state.head != 0 or "nonce-alice-7" in state.nullifiers:
        return state, False
    return (
        E08StateV1(
            head=1,
            authority_epoch=state.authority_epoch,
            phase=state.phase,
            committed_ids=tuple(sorted(state.committed_ids + (commit_id,))),
            nullifiers=tuple(sorted(state.nullifiers + ("nonce-alice-7",))),
        ),
        True,
    )


def transition(state: E08StateV1, action: str) -> E08TransitionV1:
    """Apply one named action; invalid lifecycle actions are no-op rejects."""

    if action not in E08_ACTIONS_V1:
        raise E08ModelError("action is outside the closed manifest")
    if action in {"commit_a", "retry_a"}:
        target, accepted = _commit(state, "commit-a")
    elif action in {"commit_b", "retry_b"}:
        target, accepted = _commit(state, "commit-b")
    elif action == "quiesce":
        if state.phase is E08PhaseV1.ACTIVE:
            target = E08StateV1(
                head=state.head,
                authority_epoch=state.authority_epoch,
                phase=E08PhaseV1.QUIESCED,
                committed_ids=state.committed_ids,
                nullifiers=state.nullifiers,
            )
            accepted = True
        else:
            target, accepted = state, False
    else:
        if state.phase is E08PhaseV1.QUIESCED:
            target = E08StateV1(
                head=state.head,
                authority_epoch=1,
                phase=E08PhaseV1.SWITCHED,
                committed_ids=state.committed_ids,
                nullifiers=state.nullifiers,
            )
            accepted = True
        else:
            target, accepted = state, False
    return E08TransitionV1(source=state, action=action, target=target, accepted=accepted)


def invariant_results(state: E08StateV1) -> tuple[E08Invariant, ...]:
    """Return named invariant results for one state."""

    return (
        ("unique_commit_ids", len(set(state.committed_ids)) == len(state.committed_ids)),
        ("unique_nullifiers", len(set(state.nullifiers)) == len(state.nullifiers)),
        ("head_matches_publications", state.head == len(state.committed_ids)),
        ("head_matches_nullifiers", state.head == len(state.nullifiers)),
        (
            "phase_monotone_shape",
            state.phase is not E08PhaseV1.ACTIVE or state.authority_epoch == 0,
        ),
        (
            "switch_requires_epoch",
            state.phase is not E08PhaseV1.SWITCHED or state.authority_epoch == 1,
        ),
    )


@dataclass(frozen=True, slots=True)
class E08ExplorationResultV1:
    """Frozen result of the bounded breadth-first exploration."""

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
            raise E08ModelError("exploration counts are outside the closed domain")
        if self.invariant_failures:
            raise E08ModelError("exploration reached an invariant failure")
        if tuple(sorted(self.killed_mutants)) != self.killed_mutants:
            raise E08ModelError("mutant labels must be ordered")

    def to_wire(self) -> dict[str, object]:
        return {
            "max_depth": self.max_depth,
            "action_manifest": list(E08_ACTIONS_V1),
            "reachable_states": self.reachable_states,
            "transitions": self.transitions,
            "accepted_transitions": self.accepted_transitions,
            "rejected_stutters": self.rejected_stutters,
            "invariant_checks": self.invariant_checks,
            "invariant_failures": list(self.invariant_failures),
            "killed_mutants": list(self.killed_mutants),
        }


def _check_state(state: E08StateV1) -> tuple[str, ...]:
    return tuple(name for name, passed in invariant_results(state) if not passed)


def kill_mutants() -> tuple[str, ...]:
    """Return named mutants rejected by the invariant checker."""

    killed: list[str] = []
    try:
        E08StateV1(
            head=2,
            authority_epoch=0,
            phase=E08PhaseV1.ACTIVE,
            committed_ids=("commit-a", "commit-b"),
            nullifiers=("nonce-alice-7", "nonce-alice-7"),
        )
    except E08ModelError:
        killed.append("duplicate_nullifier")
    if (
        transition(initial_state(), "quiesce").target.phase is E08PhaseV1.QUIESCED
        and not transition(transition(initial_state(), "quiesce").target, "commit_a").accepted
    ):
        killed.append("commit_after_quiescence")
    if not transition(initial_state(), "authority_switch").accepted:
        killed.append("authority_switch_without_quiescence")
    try:
        E08StateV1(
            head=2,
            authority_epoch=0,
            phase=E08PhaseV1.ACTIVE,
            committed_ids=("commit-a", "commit-b"),
            nullifiers=("nonce-alice-7", "nonce-bob-8"),
        )
    except E08ModelError:
        killed.append("retry_increments_head")
    if not transition(transition(initial_state(), "quiesce").target, "commit_a").accepted:
        killed.append("commit_after_quiescence")
    try:
        E08StateV1(
            head=1,
            authority_epoch=0,
            phase=E08PhaseV1.ACTIVE,
            committed_ids=("commit-a", "commit-b"),
            nullifiers=("nonce-alice-7",),
        )
    except E08ModelError:
        killed.append("split_publication")
    return tuple(sorted(set(killed)))


def explore(max_depth: int = E08_MAX_WORD_DEPTH_V1) -> E08ExplorationResultV1:
    """Enumerate all action words up to ``max_depth``."""

    if type(max_depth) is not int or max_depth < 0 or max_depth > E08_MAX_WORD_DEPTH_V1:
        raise E08ModelError("max_depth is outside the closed exploration bound")
    initial = initial_state()
    queue: deque[tuple[E08StateV1, int]] = deque([(initial, 0)])
    visited: set[E08StateV1] = {initial}
    transitions = 0
    accepted = 0
    rejected = 0
    invariant_checks = 0
    failures: set[str] = set()
    while queue:
        state, depth = queue.popleft()
        for action in E08_ACTIONS_V1:
            edge = transition(state, action)
            transitions += 1
            accepted += int(edge.accepted)
            rejected += int(not edge.accepted)
            failures.update(_check_state(edge.target))
            invariant_checks += len(invariant_results(edge.target))
            if depth < max_depth and edge.target not in visited:
                visited.add(edge.target)
                queue.append((edge.target, depth + 1))
    return E08ExplorationResultV1(
        max_depth=max_depth,
        reachable_states=len(visited),
        transitions=transitions,
        accepted_transitions=accepted,
        rejected_stutters=rejected,
        invariant_checks=invariant_checks,
        invariant_failures=tuple(sorted(failures)),
        killed_mutants=kill_mutants(),
    )


__all__ = (
    "E08_ACTIONS_V1",
    "E08_MAX_WORD_DEPTH_V1",
    "E08ExplorationResultV1",
    "E08ModelError",
    "E08PhaseV1",
    "E08StateV1",
    "E08TransitionV1",
    "explore",
    "initial_state",
    "invariant_results",
    "kill_mutants",
    "transition",
)
