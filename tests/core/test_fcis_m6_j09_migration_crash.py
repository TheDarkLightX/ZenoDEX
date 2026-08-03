"""Focused BDD-style tests for the public J09 migration model."""

from __future__ import annotations

from experiments.fcis_m6_j09_migration_crash_check import run_checks
from src.core.fcis_m6_j09_migration_crash import (
    J09CrashObservationV1,
    J09RejectCodeV1,
    J09StateV1,
    J09WriterV1,
    initial_state,
    invariant_results,
    transition,
)


def _apply(state: J09StateV1, action: str) -> J09StateV1:
    edge = transition(state, action)
    assert edge.accepted, (action, edge.reject_code)
    return edge.target


def test_initial_state_is_complete_and_single_writer() -> None:
    state = initial_state()
    assert all(passed for _name, passed in invariant_results(state))
    assert state.allowed_writers == (J09WriterV1.LEGACY,)
    assert state.active_writer is J09WriterV1.LEGACY


def test_phase_advancement_is_exact_and_reaches_legacy_disabled() -> None:
    state = initial_state()
    for _ in range(6):
        state = _apply(state, "advance_phase")
    assert [phase.value for phase in state.phase_trace] == [
        "LEGACY",
        "SHADOW_REPLAY",
        "DUAL_CHECK",
        "QUIESCED",
        "AUTHORITY_SWITCH",
        "POST_SWITCH_VALIDATION",
        "LEGACY_DISABLED",
    ]
    assert state.allowed_writers == (J09WriterV1.TARGET,)
    assert state.active_writer is J09WriterV1.NONE


def test_pre_crash_discards_pending_and_restart_requires_reauthorization() -> None:
    state = _apply(initial_state(), "prepare_legacy")
    state = _apply(state, "crash_pre")
    assert state.crash_observation is J09CrashObservationV1.PRE
    assert state.pending is None
    state = _apply(state, "restart")
    assert state.active_writer is J09WriterV1.NONE
    assert not state.fresh_authorization
    rejected = transition(state, "retry_legacy")
    assert not rejected.accepted
    assert rejected.reject_code is J09RejectCodeV1.STALE_TOKEN


def test_post_crash_publishes_complete_atom_and_retry_confirms() -> None:
    state = _apply(initial_state(), "prepare_legacy")
    state = _apply(state, "crash_post")
    assert state.crash_observation is J09CrashObservationV1.POST
    assert len(state.history) == 1
    assert len(state.outbox) == 1
    state = _apply(state, "restart")
    retry = transition(state, "retry_legacy")
    assert retry.accepted
    assert retry.target.retry_knowledge.value == "CONFIRMED"


def test_delivery_acknowledgment_requires_committed_outbox_and_delivery() -> None:
    state = initial_state()
    rejected = transition(state, "ack_outbox")
    assert not rejected.accepted
    assert rejected.reject_code is J09RejectCodeV1.NOT_DELIVERED
    state = _apply(state, "prepare_legacy")
    state = _apply(state, "publish_pending")
    state = _apply(state, "deliver_outbox")
    state = _apply(state, "ack_outbox")
    assert state.delivered_effect_ids == ("effect-1",)
    assert state.acknowledged_effect_ids == ("effect-1",)


def test_target_writer_and_v2_evidence_follow_switch() -> None:
    state = initial_state()
    for _ in range(4):
        state = _apply(state, "advance_phase")
    stale = transition(state, "stale_legacy_commit")
    assert not stale.accepted
    state = _apply(state, "fresh_authorize")
    state = _apply(state, "prepare_target")
    state = _apply(state, "publish_pending")
    assert state.history[0].writer is J09WriterV1.TARGET
    assert state.history[0].evidence_version.value == "V2"
    assert all(passed for _name, passed in invariant_results(state))


def test_independent_checker_and_public_vector_pass() -> None:
    payload = run_checks()
    assert payload["invariant_failures"] == []
    assert payload["reachable_states"] >= 1000
    assert len(payload["killed_mutants"]) >= 8
