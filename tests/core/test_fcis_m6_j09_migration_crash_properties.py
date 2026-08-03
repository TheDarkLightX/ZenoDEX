"""Deterministic repeatability and reject-is-no-op properties for J09."""

from __future__ import annotations

from experiments.fcis_m6_j09_migration_crash_check import run_checks
from src.core.fcis_m6_j09_migration_crash import J09_ACTIONS_V1, initial_state, transition
from src.state.canonical import canonical_json_bytes


def test_repeated_campaigns_have_identical_wire_results() -> None:
    first = run_checks()
    second = run_checks()
    assert canonical_json_bytes(first) == canonical_json_bytes(second)


def test_rejected_actions_are_typed_stutters() -> None:
    state = initial_state()
    for action in J09_ACTIONS_V1:
        edge = transition(state, action)
        if not edge.accepted:
            assert edge.target == state
            assert edge.reject_code.value != "NONE"
