"""J04 migration manifest binding and negative-witness tests."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

import pytest

from tools.check_fcis_m6_j04_migration_manifest import (
    check_manifest,
    derive_manifest_root,
)

_MANIFEST = (
    Path(__file__).resolve().parents[2]
    / "docs/research/m6_tasks/TASK_J04_MIGRATION_MANIFEST_V1.json"
)


def _payload() -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(_MANIFEST.read_text(encoding="utf-8")))


def _rebind(payload: dict[str, Any]) -> None:
    payload["manifest_root"] = derive_manifest_root(payload)


def _assert_rejected(payload: dict[str, Any], tmp_path: Path, message: str) -> None:
    mutated = tmp_path / "mutated-j04.json"
    mutated.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ValueError, match=message):
        check_manifest(mutated)


def test_j04_migration_manifest_is_complete() -> None:
    check_manifest(_MANIFEST)


def test_j04_manifest_root_binds_all_fields() -> None:
    payload = _payload()
    original = payload["manifest_root"]
    payload["activation_sequence"] = 101
    assert derive_manifest_root(payload) != original


def test_j04_rejects_same_source_and_target_configuration(tmp_path: Path) -> None:
    payload = _payload()
    payload["target_configuration_root"] = payload["source_configuration_root"]
    _rebind(payload)

    _assert_rejected(
        payload, tmp_path, "source_configuration_root and target_configuration_root must differ"
    )


def test_j04_rejects_missing_quiescence_marker(tmp_path: Path) -> None:
    payload = _payload()
    evidence = cast(list[str], payload["quiescence_evidence"])
    evidence.remove("WORKER_WRITER_QUIESCED")
    _rebind(payload)

    _assert_rejected(payload, tmp_path, "quiescence evidence is incomplete")


def test_j04_rejects_transport_row_without_checker(tmp_path: Path) -> None:
    payload = _payload()
    transport = cast(list[dict[str, Any]], payload["transport_maps"])
    transport[0]["checker_id"] = "NONE"
    _rebind(payload)

    _assert_rejected(payload, tmp_path, "transport checker is missing")


def test_j04_rejects_zero_activation_sequence(tmp_path: Path) -> None:
    payload = _payload()
    payload["activation_sequence"] = 0
    _rebind(payload)

    _assert_rejected(payload, tmp_path, "activation_sequence must be a positive u32")
