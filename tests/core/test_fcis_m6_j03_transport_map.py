"""J03 migration artifact transport map tests."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

import pytest

from tools.check_fcis_m6_j03_transport_map import check_transport_map

_MAP = Path(__file__).resolve().parents[2] / "docs/research/m6_tasks/TASK_J03_TRANSPORT_MAP_V1.json"


def _payload() -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(_MAP.read_text(encoding="utf-8")))


def _artifacts(payload: dict[str, Any]) -> list[dict[str, Any]]:
    return cast(list[dict[str, Any]], payload["artifacts"])


def _assert_rejected(payload: dict[str, Any], tmp_path: Path, message: str) -> None:
    mutated = tmp_path / "mutated-j03.json"
    mutated.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ValueError, match=message):
        check_transport_map(mutated)


def test_j03_transport_map_is_complete() -> None:
    check_transport_map(_MAP)


def test_j03_covers_all_eight_required_artifacts() -> None:
    payload = _payload()
    artifacts = _artifacts(payload)
    assert len(artifacts) == 8
    assert [artifact["artifact_id"] for artifact in artifacts] == payload["required_artifact_ids"]


def test_j03_rejects_missing_transport_root(tmp_path: Path) -> None:
    payload = _payload()
    _artifacts(payload)[0]["transport_root"] = "NONE"

    _assert_rejected(payload, tmp_path, "transport map lacks checker/root")


def test_j03_rejects_unconditioned_preservation(tmp_path: Path) -> None:
    payload = _payload()
    _artifacts(payload)[4]["preservation_condition"] = ""

    _assert_rejected(payload, tmp_path, "preservation_condition must be a nonempty string")


def test_j03_rejects_wrong_profile_boundary_mapping(tmp_path: Path) -> None:
    payload = _payload()
    _artifacts(payload)[1]["mapping"] = "PRESERVED_UNCHANGED"

    _assert_rejected(payload, tmp_path, "mapping policy mismatch for configuration")
