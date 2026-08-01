"""Fail-closed checker for the FCIS M6 I07 outbox disaster matrix."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, cast

_SCENARIO_IDS = (
    "delivery_before_local_commit",
    "orphan_outbox_row",
    "payload_collision_same_effect_id",
    "foreign_receipt_ack",
    "ack_before_delivery",
    "lost_lease",
    "worker_crash_before_send",
    "worker_crash_after_send",
    "worker_crash_after_ack_write",
    "migration_during_delivery",
)
_SCENARIO_ID_SET = frozenset(_SCENARIO_IDS)
_SCENARIO_FIELDS = frozenset(
    {
        "scenario_id",
        "trigger",
        "preconditions",
        "fault_boundary",
        "expected_durable_state",
        "expected_external_state",
        "required_invariants",
        "evidence_refs",
        "nonclaims",
    }
)
_DURABLE_FIELDS = frozenset({"reopen", "outbox", "ack", "authority"})
_EXTERNAL_FIELDS = frozenset({"delivery_attempts", "semantic_effects", "receipt"})
_REOPEN_STATES = frozenset({"ACCEPT", "REJECT"})
_OUTBOX_STATES = frozenset(
    {
        "ABSENT_OR_UNCOMMITTED",
        "ORPHAN_REJECTED",
        "COMMITTED_UNCHANGED",
        "COMMITTED_PENDING",
        "PENDING_AFTER_RECLAIM",
        "DELIVERED_UNACKED",
        "ACK_DURABLE",
    }
)
_ACK_STATES = frozenset({"ABSENT", "ABSENT_REJECTED", "ONE_DURABLE"})
_AUTHORITY_STATES = frozenset(
    {
        "NO_COMMIT",
        "RECOVERY_REJECTED",
        "UNCHANGED",
        "STALE_WRITER_REJECTED",
    }
)
_RECEIPT_STATES = frozenset(
    {
        "NO_DELIVERY",
        "PAYLOAD_CONFLICT_REJECTED",
        "FOREIGN_RECEIPT_REJECTED",
        "ACK_REJECTED",
        "ALREADY_ACCEPTED",
        "ACCEPTED",
        "DELIVERY_BLOCKED",
    }
)
_REQUIRED_INVARIANT_BY_ID = {
    "delivery_before_local_commit": "committed_outbox_precedes_delivery",
    "orphan_outbox_row": "canonical_reopen_rejects_orphan_rows",
    "payload_collision_same_effect_id": "same_effect_id_cannot_change_payload",
    "foreign_receipt_ack": "ack_receipt_must_match_effect_and_destination",
    "ack_before_delivery": "ack_requires_delivery_membership",
    "lost_lease": "lease_reclaim_preserves_effect_identity",
    "worker_crash_before_send": "expired_lease_returns_to_pending",
    "worker_crash_after_send": "redelivery_is_idempotent",
    "worker_crash_after_ack_write": "durable_ack_is_written_once",
    "migration_during_delivery": "authority_epoch_blocks_stale_delivery",
}


def _require_nonempty_string(value: object, label: str) -> None:
    if type(value) is not str or not value:
        raise ValueError(f"{label} must be a nonempty string")


def _require_nonempty_string_list(value: object, label: str) -> None:
    if type(value) is not list or not value:
        raise ValueError(f"{label} must be a nonempty list")
    if any(type(item) is not str or not item for item in value):
        raise ValueError(f"{label} must contain nonempty strings")
    if len(set(value)) != len(value):
        raise ValueError(f"{label} must not contain duplicates")


def _check_durable_state(value: object, scenario_id: str) -> None:
    if type(value) is not dict:
        raise ValueError(f"{scenario_id}.expected_durable_state must be an object")
    durable = cast(dict[str, Any], value)
    if set(durable) != _DURABLE_FIELDS:
        raise ValueError(f"{scenario_id}.expected_durable_state fields are not exact")
    reopen = durable["reopen"]
    outbox = durable["outbox"]
    ack = durable["ack"]
    authority = durable["authority"]
    if reopen not in _REOPEN_STATES:
        raise ValueError(f"{scenario_id} has an invalid reopen state")
    if outbox not in _OUTBOX_STATES:
        raise ValueError(f"{scenario_id} has an invalid outbox state")
    if ack not in _ACK_STATES:
        raise ValueError(f"{scenario_id} has an invalid ack state")
    if authority not in _AUTHORITY_STATES:
        raise ValueError(f"{scenario_id} has an invalid authority state")
    if type(reopen) is not str or type(outbox) is not str:
        raise ValueError(f"{scenario_id} durable enum values must be strings")
    if type(ack) is not str or type(authority) is not str:
        raise ValueError(f"{scenario_id} durable enum values must be strings")


def _check_external_state(value: object, scenario_id: str) -> None:
    if type(value) is not dict:
        raise ValueError(f"{scenario_id}.expected_external_state must be an object")
    external = cast(dict[str, Any], value)
    if set(external) != _EXTERNAL_FIELDS:
        raise ValueError(f"{scenario_id}.expected_external_state fields are not exact")
    attempts = external["delivery_attempts"]
    effects = external["semantic_effects"]
    receipt = external["receipt"]
    if type(attempts) is not int or attempts < 0:
        raise ValueError(f"{scenario_id} delivery_attempts must be a nonnegative integer")
    if type(effects) is not int or effects not in (0, 1):
        raise ValueError(f"{scenario_id} semantic_effects must be zero or one")
    if type(receipt) is not str or receipt not in _RECEIPT_STATES:
        raise ValueError(f"{scenario_id} has an invalid receipt state")
    if effects == 0 and receipt in {"ACCEPTED", "ALREADY_ACCEPTED"}:
        raise ValueError(f"{scenario_id} receipt claims an effect without a semantic effect")
    if attempts == 0 and effects == 1:
        raise ValueError(f"{scenario_id} claims an effect without a delivery attempt")


def check_matrix(path: Path) -> None:
    payload = cast(dict[str, Any], json.loads(path.read_text(encoding="utf-8")))
    if payload.get("schema_version") != "zenodex.fcis.m6.i07.outbox-disaster-matrix.v1":
        raise ValueError("wrong I07 matrix schema")
    if payload.get("task_id") != "I07":
        raise ValueError("wrong I07 task ID")
    if type(payload.get("scope")) is not str or not payload["scope"]:
        raise ValueError("matrix scope must be a nonempty string")
    required = payload.get("required_scenario_ids")
    if type(required) is not list or tuple(required) != _SCENARIO_IDS:
        raise ValueError("required scenario registry is incomplete or reordered")
    scenarios = payload.get("scenarios")
    if type(scenarios) is not list or len(scenarios) != len(_SCENARIO_IDS):
        raise ValueError("scenario list must contain exactly ten rows")
    seen: set[str] = set()
    for scenario in scenarios:
        if type(scenario) is not dict:
            raise ValueError("scenario row must be an object")
        if set(scenario) != _SCENARIO_FIELDS:
            raise ValueError("scenario fields are not exact")
        scenario_id = scenario["scenario_id"]
        _require_nonempty_string(scenario_id, "scenario_id")
        if scenario_id not in _SCENARIO_ID_SET or scenario_id in seen:
            raise ValueError(f"unknown or duplicate scenario ID: {scenario_id}")
        seen.add(scenario_id)
        _require_nonempty_string(scenario["trigger"], f"{scenario_id}.trigger")
        _require_nonempty_string(scenario["fault_boundary"], f"{scenario_id}.fault_boundary")
        _require_nonempty_string_list(scenario["preconditions"], f"{scenario_id}.preconditions")
        _require_nonempty_string_list(
            scenario["required_invariants"], f"{scenario_id}.required_invariants"
        )
        _require_nonempty_string_list(scenario["evidence_refs"], f"{scenario_id}.evidence_refs")
        _require_nonempty_string_list(scenario["nonclaims"], f"{scenario_id}.nonclaims")
        if "M6 remains unmounted and non-promotable" not in scenario["nonclaims"]:
            raise ValueError(f"{scenario_id} must preserve the M6 unmounted boundary")
        _check_durable_state(scenario["expected_durable_state"], scenario_id)
        _check_external_state(scenario["expected_external_state"], scenario_id)
        required_invariants = cast(list[str], scenario["required_invariants"])
        required_invariant = _REQUIRED_INVARIANT_BY_ID[scenario_id]
        if required_invariant not in required_invariants:
            raise ValueError(f"{scenario_id} is missing its named invariant")
    if seen != _SCENARIO_ID_SET:
        raise ValueError(f"scenario coverage mismatch: {sorted(_SCENARIO_ID_SET - seen)}")
    global_nonclaims_value = payload.get("global_nonclaims")
    _require_nonempty_string_list(global_nonclaims_value, "global_nonclaims")
    global_nonclaims = cast(list[str], global_nonclaims_value)
    if "M6 remains unmounted and non-promotable" not in global_nonclaims:
        raise ValueError("global nonclaims omit the unmounted M6 boundary")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_fcis_m6_i07_disaster_matrix.py <matrix.json>", file=sys.stderr)
        return 2
    try:
        check_matrix(Path(argv[1]))
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"I07_DISASTER_MATRIX_REJECT: {exc}", file=sys.stderr)
        return 1
    print("I07_DISASTER_MATRIX_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
