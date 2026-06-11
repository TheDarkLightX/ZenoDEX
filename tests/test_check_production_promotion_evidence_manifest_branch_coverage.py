"""Boundary-path tests for the production promotion manifest checker."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import check_production_promotion_evidence_manifest as checker

MANIFEST_SCHEMA = "zenodex/production-promotion-evidence-manifest/v1"


def test_load_json_rejects_bad_path_json_and_shape(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="non-empty path"):
        checker._load_json("", field_name="field", base_dir=tmp_path)

    bad_json = tmp_path / "bad.json"
    bad_json.write_text("{")
    with pytest.raises(ValueError, match="invalid JSON"):
        checker._load_json("bad.json", field_name="field", base_dir=tmp_path)

    list_json = tmp_path / "list.json"
    list_json.write_text("[]")
    with pytest.raises(ValueError, match="JSON object"):
        checker._load_json("list.json", field_name="field", base_dir=tmp_path)


def test_load_json_resolves_relative_paths_from_manifest_dir(tmp_path: Path) -> None:
    sidecar = tmp_path / "sidecar.json"
    sidecar.write_text(json.dumps({"ok": True}), encoding="utf-8")

    loaded = checker._load_json("sidecar.json", field_name="field", base_dir=tmp_path)

    assert loaded == {"ok": True}


def test_optional_object_missing_key_returns_empty() -> None:
    assert checker._optional_object({}, key="config") == {}


def test_lane_scoped_output_missing_lane_rejects_stably() -> None:
    out = checker._lane_scoped_output({"schema": "s", "lanes": {}}, "oracle_authority")
    assert out["promotion_ready"] is False
    assert out["blocked_lanes"] == ["oracle_authority"]


def test_load_manifest_error_shapes(tmp_path: Path) -> None:
    missing_manifest, missing_error = checker._load_manifest(tmp_path / "missing.json")
    assert missing_manifest is None
    assert missing_error is not None
    assert missing_error["error"] == "manifest_not_found"

    bad_json = tmp_path / "bad-manifest.json"
    bad_json.write_text("{")
    _, bad_error = checker._load_manifest(bad_json)
    assert bad_error is not None
    assert bad_error["error"] == "manifest_invalid_json"

    list_manifest = tmp_path / "list-manifest.json"
    list_manifest.write_text("[]")
    _, list_error = checker._load_manifest(list_manifest)
    assert list_error is not None
    assert list_error["error"] == "manifest_not_object"

    wrong_schema = tmp_path / "wrong-schema.json"
    wrong_schema.write_text(json.dumps({"schema": "wrong"}))
    _, schema_error = checker._load_manifest(wrong_schema)
    assert schema_error is not None
    assert schema_error["error"] == "manifest_schema_mismatch"


def test_main_manifest_load_error_prints_stable_json(capsys, tmp_path: Path) -> None:
    assert checker.main([str(tmp_path / "missing.json")]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_not_found"


def test_main_manifest_config_invalid_for_bad_json_sidecar(capsys, tmp_path: Path) -> None:
    sidecar = tmp_path / "sidecar.json"
    sidecar.write_text("{")
    manifest = tmp_path / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "schema": MANIFEST_SCHEMA,
                "config": {"bounded_oracle_exercise_status_path": "sidecar.json"},
                "bundle": {},
            }
        )
    )

    assert checker.main([str(manifest)]) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["error"] == "manifest_config_invalid"
    assert "invalid JSON" in out["detail"]


def test_exit_code_uses_bundle_status_when_no_lane() -> None:
    assert checker._exit_code({"promotion_ready": True}, lane=None) == 0
    assert checker._exit_code({"promotion_ready": False}, lane=None) == 1
