"""Independent deterministic checks for the E06 concurrency campaign."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from experiments.fcis_m6_e06_concurrency import run_campaign
from src.state.canonical import canonical_json_bytes

_ROOT = Path(__file__).resolve().parents[1]
_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_E06_CONCURRENCY_V1.json"
_SCHEMA = "zenodex/fcis/m6/e06/concurrency/v1"


def build_payload() -> dict[str, object]:
    observations = run_campaign()
    return {
        "schema": _SCHEMA,
        "worker_count": 2,
        "observations": [observation.to_wire() for observation in observations],
    }


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    payload = build_payload()
    repeated = build_payload()
    if canonical_json_bytes(payload) != canonical_json_bytes(repeated):
        raise AssertionError("E06 concurrency campaign is not repeatable")
    observations = cast(list[object], payload["observations"])
    if len(observations) != 5:
        raise AssertionError("E06 campaign does not cover all five required races")
    if check_vector:
        expected = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: E06 concurrency vector is stale")
    return payload


def main() -> None:
    payload = run_checks()
    observations = cast(list[object], payload["observations"])
    print(f"E06_CONCURRENCY_CHECKS_PASS {len(observations)}")


if __name__ == "__main__":
    main()
