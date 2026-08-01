"""K04 D05/K01 topology-anchor tests."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

from experiments.fcis_m6_k04_topology_anchor_check import run_checks
from tools.build_fcis_m6_k04_topology_anchor import (
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    build_payload,
)

_ROOT = Path(__file__).resolve().parents[2]


def test_k04_deterministic_anchor_checker_passes() -> None:
    run_checks()


def test_k04_vector_is_pinned_and_matches_regeneration() -> None:
    payload = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    assert payload["pinned_topology_anchor_root"] == payload["topology_anchor_root"]
    assert payload == build_payload(_ROOT / DEFAULT_CONFIG_PATH)


def test_k04_root_is_sensitive_to_publisher_and_source_drift() -> None:
    payload = build_payload(_ROOT / DEFAULT_CONFIG_PATH)
    assert len(cast(list[object], payload["publisher_ids"])) == 15
    assert len(cast(list[object], payload["source_paths"])) >= 20
