from __future__ import annotations

from pathlib import Path

import pytest

import src.fire.verifier.formal_assurance_claims_v1 as formal_claims
import src.fire.verifier.release_assurance_v1 as release_assurance


def test_fire_json_loaders_wrap_bad_manifest_syntax(tmp_path: Path) -> None:
    path = tmp_path / "bad.json"
    path.write_text("{", encoding="utf-8")

    with pytest.raises(formal_claims.FireFormalAssuranceClaimsError, match="failed to read JSON"):
        formal_claims._load_json(path)
    with pytest.raises(release_assurance.FireReleaseAssuranceError, match="failed to read JSON"):
        release_assurance._load_json(path)


def test_fire_yaml_loaders_wrap_bad_manifest_syntax(tmp_path: Path) -> None:
    path = tmp_path / "bad.yaml"
    path.write_text("x: [", encoding="utf-8")

    with pytest.raises(formal_claims.FireFormalAssuranceClaimsError, match="failed to read YAML"):
        formal_claims._load_yaml(path)
    with pytest.raises(release_assurance.FireReleaseAssuranceError, match="failed to read YAML"):
        release_assurance._load_yaml(path)


def test_fire_json_loaders_propagate_unexpected_parser_failures(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    path = tmp_path / "ok.json"
    path.write_text("{}", encoding="utf-8")

    def broken_loads(_text: str) -> object:
        raise RuntimeError("broken JSON parser")

    monkeypatch.setattr(formal_claims.json, "loads", broken_loads)

    with pytest.raises(RuntimeError, match="broken JSON parser"):
        formal_claims._load_json(path)
    with pytest.raises(RuntimeError, match="broken JSON parser"):
        release_assurance._load_json(path)


def test_fire_yaml_loaders_propagate_unexpected_parser_failures(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    path = tmp_path / "ok.yaml"
    path.write_text("{}", encoding="utf-8")

    def broken_safe_load(_text: str) -> object:
        raise RuntimeError("broken YAML parser")

    monkeypatch.setattr(formal_claims.yaml, "safe_load", broken_safe_load)

    with pytest.raises(RuntimeError, match="broken YAML parser"):
        formal_claims._load_yaml(path)
    with pytest.raises(RuntimeError, match="broken YAML parser"):
        release_assurance._load_yaml(path)
