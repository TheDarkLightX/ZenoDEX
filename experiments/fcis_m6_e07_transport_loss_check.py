"""Independent deterministic checks for the E07 transport-loss campaign."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from experiments.fcis_m6_e07_transport_loss import run_campaign
from src.state.canonical import canonical_json_bytes

_ROOT = Path(__file__).resolve().parents[1]
_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_E07_TRANSPORT_LOSS_V1.json"
_SCHEMA = "zenodex/fcis/m6/e07/transport-loss/v1"


def build_payload() -> dict[str, object]:
    observations = run_campaign()
    return {
        "schema": _SCHEMA,
        "loss_point_count": len(observations),
        "observations": [observation.to_wire() for observation in observations],
    }


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    payload = build_payload()
    repeated = build_payload()
    if canonical_json_bytes(payload) != canonical_json_bytes(repeated):
        raise AssertionError("E07 transport campaign is not repeatable")
    observations = cast(list[object], payload["observations"])
    if len(observations) != 4:
        raise AssertionError("E07 loss-point manifest is incomplete")
    if check_vector:
        expected = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: E07 transport-loss vector is stale")
    return payload


def main() -> None:
    payload = run_checks()
    print(f"E07_TRANSPORT_LOSS_CHECKS_PASS {payload['loss_point_count']}")


if __name__ == "__main__":
    main()
