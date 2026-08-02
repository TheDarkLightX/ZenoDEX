"""Focused E08 public finite-state model tests."""

from __future__ import annotations

import pytest

from experiments.fcis_m6_e08_finite_state import (
    E08ModelError,
    E08PhaseV1,
    E08StateV1,
    explore,
    initial_state,
    transition,
)


def test_bounded_explorer_has_no_safe_invariant_failure() -> None:
    result = explore()

    assert result.reachable_states == 9
    assert result.transitions == 54
    assert result.accepted_transitions == 10
    assert result.rejected_stutters == 44
    assert result.invariant_checks == 324
    assert result.invariant_failures == ()
    assert result.killed_mutants == (
        "authority_switch_without_quiescence",
        "commit_after_quiescence",
        "duplicate_nullifier",
        "retry_increments_head",
        "split_publication",
    )


def test_commit_and_exact_retry_are_atomic_stutters() -> None:
    committed = transition(initial_state(), "commit_a")
    retried = transition(committed.target, "retry_a")

    assert committed.accepted is True
    assert retried.accepted is False
    assert retried.target == committed.target
    assert committed.target.committed_ids == ("commit-a",)
    assert committed.target.nullifiers == ("nonce-alice-7",)


def test_quiescence_and_authority_switch_block_value_transition() -> None:
    quiesced = transition(initial_state(), "quiesce").target
    switched = transition(quiesced, "authority_switch").target

    assert quiesced.phase is E08PhaseV1.QUIESCED
    assert switched.phase is E08PhaseV1.SWITCHED
    assert transition(quiesced, "commit_a").accepted is False
    assert transition(switched, "commit_a").accepted is False


def test_invalid_action_and_invalid_state_fail_closed() -> None:
    with pytest.raises(E08ModelError, match="manifest"):
        transition(initial_state(), "unknown")
    with pytest.raises(E08ModelError, match="unique"):
        E08StateV1(
            head=1,
            authority_epoch=0,
            phase=E08PhaseV1.ACTIVE,
            committed_ids=("commit-a",),
            nullifiers=("nonce-alice-7", "nonce-alice-7"),
        )
