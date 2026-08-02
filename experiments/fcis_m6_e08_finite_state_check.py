"""Independent deterministic checks for the E08 public finite-state model."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from experiments.fcis_m6_e08_finite_state import (
    E08_ACTIONS_V1,
    E08_MAX_WORD_DEPTH_V1,
    explore,
)
from src.state.canonical import canonical_json_bytes

_ROOT = Path(__file__).resolve().parents[1]
_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_E08_FINITE_STATE_V1.json"
_SCHEMA = "zenodex/fcis/m6/e08/finite-state/v1"


def build_payload() -> dict[str, object]:
    result = explore()
    payload = cast(dict[str, object], result.to_wire())
    payload["schema"] = _SCHEMA
    return payload


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    payload = build_payload()
    repeated = build_payload()
    if canonical_json_bytes(payload) != canonical_json_bytes(repeated):
        raise AssertionError("E08 finite-state exploration is not repeatable")
    if payload["max_depth"] != E08_MAX_WORD_DEPTH_V1:
        raise AssertionError("E08 depth is not the declared public bound")
    if payload["action_manifest"] != list(E08_ACTIONS_V1):
        raise AssertionError("E08 action manifest drifted")
    if payload["invariant_failures"] != []:
        raise AssertionError("E08 found an invariant failure")
    mutants = cast(list[object], payload["killed_mutants"])
    if len(mutants) != 5:
        raise AssertionError("E08 did not kill all declared model mutants")
    if check_vector:
        expected = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: E08 finite-state vector is stale")
    return payload


def main() -> None:
    payload = run_checks()
    print(
        "E08_FINITE_STATE_CHECKS_PASS",
        payload["reachable_states"],
        payload["transitions"],
    )


if __name__ == "__main__":
    main()
