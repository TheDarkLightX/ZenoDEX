from __future__ import annotations

import json
from pathlib import Path

import pytest

import tools.check_autogovnext_governance_lane_assurance_manifest as manifest_checker
from tools.check_autogovnext_governance_lane_assurance_manifest import (
    DEFAULT_MANIFEST,
    ManifestError,
    check_manifest,
)


def _copy_manifest(tmp_path: Path) -> Path:
    dst = tmp_path / "manifest.json"
    dst.write_text(DEFAULT_MANIFEST.read_text(encoding="utf-8"), encoding="utf-8")
    return dst


def _load(path: Path) -> dict[str, object]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(obj, dict)
    return obj


def _write(path: Path, obj: object) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def test_autogovnext_governance_lane_manifest_accepts_current_metadata() -> None:
    report = check_manifest(manifest_path=DEFAULT_MANIFEST)

    assert report["ok"] is True
    assert report["production_security_claim"] is False
    assert report["source_file_count"] >= 1


def test_autogovnext_governance_lane_manifest_rejects_source_hash_tamper(tmp_path: Path) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    source_files = manifest["source_files"]
    assert isinstance(source_files, list) and source_files
    first = source_files[0]
    assert isinstance(first, dict)
    first["sha256"] = "0" * 64
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="source hash mismatch"):
        check_manifest(manifest_path=manifest_path)


def test_autogovnext_governance_lane_manifest_rejects_untracked_source(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(manifest_checker, "_is_git_tracked", lambda _rel: False)

    with pytest.raises(ManifestError, match="not git-tracked"):
        check_manifest(manifest_path=DEFAULT_MANIFEST)


def test_autogovnext_governance_lane_manifest_rejects_production_claim_flip(tmp_path: Path) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    manifest["production_security_claim"] = True
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="production_security_claim"):
        check_manifest(manifest_path=manifest_path)


@pytest.mark.parametrize("manifest_version", [True, "1"])
def test_autogovnext_governance_lane_manifest_rejects_coerced_manifest_version(
    tmp_path: Path,
    manifest_version: object,
) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    manifest["manifest_version"] = manifest_version
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="manifest_version: expected int"):
        check_manifest(manifest_path=manifest_path)


def test_autogovnext_governance_lane_manifest_requires_upgrade_authority_non_claim(tmp_path: Path) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    non_claims = manifest["non_claims"]
    assert isinstance(non_claims, list)
    manifest["non_claims"] = [
        item for item in non_claims if item != "does_not_replace_governance_authority_for_upgrade_actions"
    ]
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="does_not_replace_governance_authority_for_upgrade_actions"):
        check_manifest(manifest_path=manifest_path)


def test_autogovnext_governance_lane_manifest_rejects_missing_focused_pytest(tmp_path: Path) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    commands = manifest["required_commands"]
    assert isinstance(commands, list)
    manifest["required_commands"] = [
        command for command in commands if isinstance(command, dict) and command.get("id") != "focused_pytest"
    ]
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="missing required command"):
        check_manifest(manifest_path=manifest_path)


def test_autogovnext_governance_lane_manifest_rejects_missing_lean_check(tmp_path: Path) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    commands = manifest["required_commands"]
    assert isinstance(commands, list)
    manifest["required_commands"] = [
        command for command in commands if isinstance(command, dict) and command.get("id") != "lean_bounded_drift"
    ]
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="missing required command"):
        check_manifest(manifest_path=manifest_path)


def test_autogovnext_governance_lane_manifest_rejects_missing_proof_client_check(tmp_path: Path) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    commands = manifest["required_commands"]
    assert isinstance(commands, list)
    manifest["required_commands"] = [
        command for command in commands if isinstance(command, dict) and command.get("id") != "ui_sdk_tests"
    ]
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="missing required command"):
        check_manifest(manifest_path=manifest_path)


@pytest.mark.parametrize("expected_exit", [False, "0"])
def test_autogovnext_governance_lane_manifest_rejects_coerced_expected_exit(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    expected_exit: object,
) -> None:
    monkeypatch.setattr(manifest_checker, "_check_source_files", lambda _entries: [])
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    commands = manifest["required_commands"]
    assert isinstance(commands, list)
    for command in commands:
        assert isinstance(command, dict)
        if command.get("id") == "focused_pytest":
            command["expected_exit"] = expected_exit
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="focused_pytest: expected_exit: expected int"):
        check_manifest(manifest_path=manifest_path)


def test_autogovnext_governance_lane_manifest_run_commands_fails_closed(tmp_path: Path) -> None:
    manifest_path = _copy_manifest(tmp_path)
    manifest = _load(manifest_path)
    commands = manifest["required_commands"]
    assert isinstance(commands, list)
    for command in commands:
        assert isinstance(command, dict)
        if command.get("id") == "focused_pytest":
            command["argv"] = ["{python}", "-c", "raise SystemExit(7)"]
    _write(manifest_path, manifest)

    with pytest.raises(ManifestError, match="focused_pytest: exit 7"):
        check_manifest(manifest_path=manifest_path, run_commands=True)
