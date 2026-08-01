"""I07 outbox disaster matrix checker and negative-witness tests."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

import pytest

from tools.check_fcis_m6_i07_disaster_matrix import check_matrix

_MATRIX = (
    Path(__file__).resolve().parents[2]
    / "docs/research/m6_tasks/TASK_I07_OUTBOX_DISASTER_MATRIX_V1.json"
)


def _payload() -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(_MATRIX.read_text(encoding="utf-8")))


def _scenarios(payload: dict[str, Any]) -> list[dict[str, Any]]:
    return cast(list[dict[str, Any]], payload["scenarios"])


def _assert_rejected(
    payload: dict[str, Any],
    tmp_path: Path,
    message: str,
) -> None:
    mutated = tmp_path / "mutated-i07.json"
    mutated.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match=message):
        check_matrix(mutated)


def test_i07_disaster_matrix_is_complete_and_exact() -> None:
    check_matrix(_MATRIX)


def test_i07_matrix_has_all_ten_named_scenarios() -> None:
    payload = _payload()
    scenarios = _scenarios(payload)
    required = cast(list[str], payload["required_scenario_ids"])
    assert len(scenarios) == 10
    assert {cast(str, scenario["scenario_id"]) for scenario in scenarios} == set(required)


def test_i07_matrix_rejects_missing_scenario(tmp_path: Path) -> None:
    payload = _payload()
    _scenarios(payload).pop()

    _assert_rejected(payload, tmp_path, "scenario list must contain exactly ten rows")


def test_i07_matrix_rejects_impossible_effect_without_attempt(tmp_path: Path) -> None:
    payload = _payload()
    external = cast(dict[str, Any], _scenarios(payload)[0]["expected_external_state"])
    external.update({"semantic_effects": 1})

    _assert_rejected(payload, tmp_path, ".*claims an effect without a delivery attempt")


def test_i07_matrix_rejects_missing_unmounted_nonclaim(tmp_path: Path) -> None:
    payload = _payload()
    nonclaims = cast(list[str], _scenarios(payload)[3]["nonclaims"])
    nonclaims.remove("M6 remains unmounted and non-promotable")

    _assert_rejected(payload, tmp_path, "must preserve the M6 unmounted boundary")


def test_i07_matrix_rejects_missing_named_invariant(tmp_path: Path) -> None:
    payload = _payload()
    invariants = cast(list[str], _scenarios(payload)[7]["required_invariants"])
    invariants.remove("redelivery_is_idempotent")

    _assert_rejected(payload, tmp_path, "is missing its named invariant")
