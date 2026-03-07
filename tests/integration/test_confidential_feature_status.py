from __future__ import annotations

import json


def test_load_confidential_feature_status_from_env_defaults(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.delenv("CONFIDENTIAL_FEATURE_STAGE", raising=False)
    monkeypatch.delenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", raising=False)
    monkeypatch.delenv("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", raising=False)

    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.stage == "beta"
    assert public["beta_ready"] is False
    assert public["default_enabled"] is False
    assert public["approved_measurements_count"] == 0
    assert "approved measurement allowlist is empty" in public["readiness_gaps"]
    assert "operator contact is missing or placeholder" in public["readiness_gaps"]


def test_load_confidential_feature_status_merges_env_and_file(monkeypatch, tmp_path) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    path = tmp_path / "measurements.json"
    path.write_text(json.dumps({"approved_measurements": ["nitro:pcr0:aa:pcr8:bb", "azure-sevsnp:hostdata:cc"]}), encoding="utf-8")
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", str(path))
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", "nitro:pcr0:aa:pcr8:bb, custom:edge")
    monkeypatch.setenv("CONFIDENTIAL_OPERATOR_CONTACT", "confidential@zenodex.test")

    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.operator_contact == "confidential@zenodex.test"
    assert public["approved_measurements_count"] == 3
    assert public["beta_ready"] is True
    assert public["readiness_gaps"] == []
    assert sorted(public["providers"]) == ["azure-sevsnp", "custom", "nitro"]


def test_load_confidential_feature_status_invalid_stage_falls_back_to_beta(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_FEATURE_STAGE", "ship-it")
    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.stage == "experimental"
    assert public["beta_ready"] is False
    assert "feature stage is experimental, not beta/ga" in public["readiness_gaps"]


def test_load_confidential_feature_status_unreadable_measurement_file_fails_closed(monkeypatch, tmp_path) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    path = tmp_path / "measurements.json"
    path.write_text('["nitro:pcr0:aa:pcr8:bb"]', encoding="utf-8")
    path.chmod(0)
    try:
        monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", str(path))
        status = load_confidential_feature_status_from_env()
        public = status.to_public_dict()
        assert public["approved_measurements_count"] == 0
        assert public["beta_ready"] is False
    finally:
        path.chmod(0o600)
