"""Fail-closed structural checker for the H07 abstract-to-SQL matrix."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, cast

_REQUIRED_ACTIONS = frozenset(
    {
        "DRA-INIT",
        "DRA-REOPEN",
        "DRA-PUBLISH",
        "DRA-AUTHORITY-APPEND",
        "DRA-ACK",
        "DRA-RETRY",
        "DRA-CRASH-RECOVERY",
        "DRA-DURABILITY",
        "DRA-EFFECT-DELIVERY",
    }
)
_REQUIRED_FIELDS = frozenset(
    {
        "action_id",
        "abstract_action",
        "status",
        "sql_transaction",
        "isolation_assumptions",
        "uniqueness_constraints",
        "recovery_behavior",
        "test_evidence",
        "nonclaims",
    }
)
_ALLOWED_STATUS = frozenset(
    {"MAPPED", "MAPPED_WITH_FIXTURE_GAP", "MAPPED_WITH_MOUNT_GAP", "OPEN_NONCLAIM"}
)


def check_matrix(path: Path) -> None:
    payload = cast(dict[str, Any], json.loads(path.read_text(encoding="utf-8")))
    if payload.get("schema_version") != "zenodex.fcis.m6.h07.refinement-matrix.v1":
        raise ValueError("wrong H07 matrix schema")
    if payload.get("task_id") != "H07":
        raise ValueError("wrong H07 task ID")
    actions = payload.get("actions")
    if type(actions) is not list:
        raise ValueError("actions must be a list")
    required = payload.get("required_action_ids")
    if type(required) is not list or set(required) != _REQUIRED_ACTIONS:
        raise ValueError("required action registry is incomplete or changed")
    seen: set[str] = set()
    for action in actions:
        if type(action) is not dict:
            raise ValueError("action row must be an object")
        missing = _REQUIRED_FIELDS.difference(action)
        if missing:
            raise ValueError(f"action missing fields: {sorted(missing)}")
        action_id = action["action_id"]
        if type(action_id) is not str or action_id in seen:
            raise ValueError("action IDs must be unique strings")
        seen.add(action_id)
        if action["status"] not in _ALLOWED_STATUS:
            raise ValueError(f"unsupported status for {action_id}")
        for field in (
            "isolation_assumptions",
            "uniqueness_constraints",
            "test_evidence",
            "nonclaims",
        ):
            if type(action[field]) is not list or not action[field]:
                raise ValueError(f"{action_id}.{field} must be nonempty")
        for field in (
            "abstract_action",
            "sql_transaction",
            "recovery_behavior",
        ):
            if type(action[field]) is not str or not action[field]:
                raise ValueError(f"{action_id}.{field} must be nonempty")
    if seen != _REQUIRED_ACTIONS:
        raise ValueError(f"action coverage mismatch: {sorted(seen ^ _REQUIRED_ACTIONS)}")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_fcis_m6_h07_refinement_matrix.py <matrix.json>", file=sys.stderr)
        return 2
    try:
        check_matrix(Path(argv[1]))
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"H07_REFINEMENT_MATRIX_REJECT: {exc}", file=sys.stderr)
        return 1
    print("H07_REFINEMENT_MATRIX_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
