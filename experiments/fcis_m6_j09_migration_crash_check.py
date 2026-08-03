"""Independent checker and vector builder for the J09 migration model."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

from src.core.fcis_m6_j09_migration_crash import (
    J09_ACTIONS_V1,
    J09_MAX_HISTORY_V1,
    J09_MAX_WORD_DEPTH_V1,
    J09EvidenceVersionV1,
    J09PhaseV1,
    J09RejectCodeV1,
    J09StateV1,
    explore,
    initial_state,
    transition,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_J09_MIGRATION_CRASH_V1.json"
CONFIG_PATH = ROOT / "config/deploy/fcis_m6_j09_migration_crash_v1.json"
SCHEMA = "zenodex/fcis/m6/j09/migration-crash-vector/v1"


def _apply(state: J09StateV1, action: str) -> J09StateV1:
    edge = transition(state, action)
    if not edge.accepted:
        raise AssertionError(f"expected {action} to be accepted, got {edge.reject_code.value}")
    return edge.target


def _reject(state: J09StateV1, action: str, code: J09RejectCodeV1) -> None:
    edge = transition(state, action)
    if edge.accepted or edge.reject_code is not code or edge.target != state:
        raise AssertionError(f"expected typed {action} rejection {code.value}")


def _scenario_checks() -> dict[str, object]:
    state = initial_state()
    _reject(state, "ack_outbox", J09RejectCodeV1.NOT_DELIVERED)
    state = _apply(state, "prepare_legacy")
    pending_before_pre = state.pending is not None
    state = _apply(state, "crash_pre")
    pre_observed = state.crash_observation.value == "PRE" and state.pending is None
    state = _apply(state, "restart")
    restart_quiesced = state.active_writer.value == "NONE" and not state.fresh_authorization
    state = _apply(state, "fresh_authorize")
    state = _apply(state, "retry_legacy")
    state = _apply(state, "crash_post")
    post_published = len(state.history) == 1 and state.crash_observation.value == "POST"
    state = _apply(state, "restart")
    retry_confirmed = _apply(state, "retry_legacy").retry_knowledge.value == "CONFIRMED"

    delivered_state = _apply(state, "deliver_outbox")
    acknowledged_state = _apply(delivered_state, "ack_outbox")
    delivery_order = (
        acknowledged_state.outbox[0].status.value == "ACKED"
        and acknowledged_state.delivered_effect_ids == ("effect-1",)
        and acknowledged_state.acknowledged_effect_ids == ("effect-1",)
    )

    switch_state = initial_state()
    for _ in range(4):
        switch_state = _apply(switch_state, "advance_phase")
    stale_edge = transition(switch_state, "stale_legacy_commit")
    stale_rejected = (
        not stale_edge.accepted
        and stale_edge.reject_code is J09RejectCodeV1.STALE_TOKEN
        and stale_edge.target == switch_state
    )
    switch_state = _apply(switch_state, "fresh_authorize")
    switch_state = _apply(switch_state, "prepare_target")
    switch_state = _apply(switch_state, "publish_pending")
    target_commit = (
        switch_state.history[-1].writer.value == "TARGET"
        and switch_state.history[-1].evidence_version is J09EvidenceVersionV1.V2
    )
    for _ in range(2):
        switch_state = _apply(switch_state, "advance_phase")
    terminal_phase = switch_state.phase is J09PhaseV1.LEGACY_DISABLED

    return {
        "all_phases_reached": terminal_phase,
        "pre_crash_discards_pending": pending_before_pre and pre_observed,
        "post_crash_publishes_pending": post_published,
        "restart_requires_fresh_authorization": restart_quiesced,
        "same_attempt_retry_confirms": retry_confirmed,
        "delivery_precedes_ack": delivery_order,
        "stale_legacy_action_rejected_after_switch": stale_rejected,
        "target_commit_uses_v2": target_commit,
        "complete_history_length": len(switch_state.history),
        "terminal_phase": switch_state.phase.value,
    }


def _read_config() -> dict[str, Any]:
    value = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("J09 config is not an object")
    return cast(dict[str, Any], value)


def build_payload() -> dict[str, object]:
    result = explore()
    payload = result.to_wire()
    payload.update(
        {
            "schema": SCHEMA,
            "profile_id": "research-unmounted-j09-migration-crash",
            "scenario_checks": _scenario_checks(),
            "max_history": J09_MAX_HISTORY_V1,
            "tla_module": "formal/tla/FCISM6J09MigrationCrash.tla",
            "tla_config": "formal/tla/FCISM6J09MigrationCrash.cfg",
        }
    )
    return payload


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    payload = build_payload()
    repeated = build_payload()
    if canonical_json_bytes(payload) != canonical_json_bytes(repeated):
        raise AssertionError("J09 exploration is not deterministic")
    if payload["max_depth"] != J09_MAX_WORD_DEPTH_V1:
        raise AssertionError("J09 depth is not the declared public bound")
    if payload["action_manifest"] != list(J09_ACTIONS_V1):
        raise AssertionError("J09 action manifest drifted")
    if payload["phase_manifest"] != [phase.value for phase in J09PhaseV1]:
        raise AssertionError("J09 phase manifest drifted")
    if payload["invariant_failures"] != []:
        raise AssertionError("J09 found an invariant failure")
    mutants = cast(list[object], payload["killed_mutants"])
    required_mutants = {
        "dual_writers",
        "missing_residual_transport",
        "mixed_v1_v2_evidence",
        "skipped_phase",
    }
    if not required_mutants.issubset(set(mutants)):
        raise AssertionError("J09 did not kill every required mutant")
    scenarios = cast(dict[str, object], payload["scenario_checks"])
    if not all(
        value is True or type(value) is int or type(value) is str for value in scenarios.values()
    ):
        raise AssertionError("J09 scenario result has an invalid type")
    if not all(
        value is True
        for key, value in scenarios.items()
        if key not in {"complete_history_length", "terminal_phase"}
    ):
        raise AssertionError("J09 scenario campaign failed")
    config = _read_config()
    if config["max_depth"] != J09_MAX_WORD_DEPTH_V1:
        raise AssertionError("J09 config depth drifted")
    if config["action_manifest"] != list(J09_ACTIONS_V1):
        raise AssertionError("J09 config actions drifted")
    if config["phase_manifest"] != [phase.value for phase in J09PhaseV1]:
        raise AssertionError("J09 config phases drifted")
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: J09 migration-crash vector is stale")
    return payload


def main() -> None:
    payload = run_checks()
    print(
        "J09_MIGRATION_CRASH_CHECKS_PASS",
        payload["reachable_states"],
        payload["transitions"],
    )


if __name__ == "__main__":
    main()
